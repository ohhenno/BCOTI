#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

#include "driver/gpio.h"
#include "driver/adc.h"

#include "nvs.h"
#include "nvs_flash.h"

#include "esp_wifi.h"
#include "esp_event.h"
#include "esp_netif.h"
#include "esp_http_server.h"

#include "Mini2.h"

// ============================================================
// WiFi Access Point settings
// Connect to this network, then open http://192.168.4.1
// ============================================================
#define WIFI_AP_SSID      "BCOTI-QC"
#define WIFI_AP_PASS      "thermal123"   // min 8 chars for WPA2
#define WIFI_AP_CHANNEL   1
#define WIFI_AP_MAX_CONN  4

static uint32_t last_click_time = 0;
static bool waiting_for_second_click = false;
static bool swallow_next_release = false;

static uint32_t mode_change_count = 0;
static uint32_t nuc_count = 0;
static uint32_t pan_count = 0;
static uint32_t brightness_count = 0;

static bool test_up = false;
static bool test_down = false;
static bool test_left = false;
static bool test_right = false;
static bool test_center = false;

static bool test_zoom = false;
static bool test_mode = false;
static bool test_nuc = false;
static bool test_brightness = false;

static int adc_min = 4095;
static int adc_max = 0;

#define DOUBLE_WINDOW_MS 400

#define PIN_CENTER     GPIO_NUM_0
#define PIN_LEFT       GPIO_NUM_3
#define PIN_UP         GPIO_NUM_10
#define PIN_RIGHT      GPIO_NUM_9
#define PIN_DOWN       GPIO_NUM_8

#define PIN_UART_TX    GPIO_NUM_1
#define PIN_UART_RX    GPIO_NUM_2

#define PAN_REPEAT_MS      40
#define TUNE_REPEAT_MS     60
#define SAVE_DELAY_MS    2000
#define NUC_PRESS_MS     3000
#define CENTER_PRESS_MS  6000

#define DEBOUNCE_MS        30
#define DPAD_LOCKOUT_MS   150

#define BRIGHT_MIN_INTERVAL_MS 150
#define BRIGHT_DEADBAND         3

// "Double-max sweep" gesture: turn the brightness knob to its extreme,
// let it fall away, then hit that same extreme again within the window
// -- this cycles the active mode/preset, same trick as the center-button
// double click. Thresholds are on raw ADC counts (pre direction-reversal),
// so ENTER is the low-raw / max-brightness end. This runs off a fast,
// lightly-smoothed reading (see adc_fast below) rather than the heavily
// filtered adc_filtered used for brightness output -- that filter has a
// multi-sample settle time that was eating quick flicks to the end.
#define KNOB_GESTURE_ENTER_RAW   500    // fast-filtered ADC <= this = "at max"
#define KNOB_GESTURE_EXIT_RAW    700    // must rise above this to re-arm
#define KNOB_GESTURE_WINDOW_MS  1200    // whole gesture must land in this window

#define ZOOM_MIN      10      // 1.0x
#define ZOOM_MAX      20      // 2.0x
static uint8_t zoom_level = 10;

#define PAN_STEP            1

#define ALIGN_CENTER_X   128
#define ALIGN_CENTER_Y    96

#define ALIGN_X_MIN      116
#define ALIGN_X_MAX      140

#define ALIGN_Y_MIN       87
#define ALIGN_Y_MAX      105

static Mini2_t cam;

typedef struct
{
    enum PseudoColor pseudo_color;
    enum SceneMode scene_mode;
    uint8_t contrast;
    uint8_t edge;
    uint8_t detail;
} preset_t;

static preset_t presets[3] =
{
    {
        .pseudo_color = WHOT,
        .scene_mode = Highlight,
        .contrast = 100,
        .edge = 1,
        .detail = 55
    },

    {
        .pseudo_color = WHOT,
        .scene_mode = HighContrast,
        .contrast = 100,
        .edge = 1,
        .detail = 55
    },

    {
        .pseudo_color = WHOT,
        .scene_mode = Outline,
        .contrast = 100,
        .edge = 1,
        .detail = 50
    }
};

// Default startup configuration is preset index 2 (Outline mode).
// This only matters on a fresh boot with no saved NVS preference --
// load_settings() will override it with whatever preset was last
// saved, if any.
static uint8_t active_preset = 2;

// Live tuning state (what the camera is currently set to).
// Initialized from the active preset, edited live via the
// web UI, and copied back into presets[] on "save preset".
static uint8_t cur_contrast = 100;
static uint8_t cur_edge = 1;
static uint8_t cur_detail = 55;
static enum SceneMode cur_scene = Highlight;
static enum PseudoColor cur_palette = WHOT;
static enum FlipMode cur_flip = No_Flip;
static bool cur_cross = false;

static uint16_t zoom_x = 128;
static uint16_t zoom_y = 96;

static uint8_t brightness = 50;
static uint8_t last_brightness = 255;
static uint32_t last_brightness_cmd = 0;
static int adc_filtered = -1;

// Fast, lightly-smoothed ADC reading used only for the knob gesture below.
// adc_filtered (heavy 7/8 IIR) is deliberately slow so brightness output
// doesn't jitter; that same slowness meant it often never reached the
// gesture thresholds during a quick flick. This settles in ~1-2 samples
// instead of ~8, while still knocking down single-sample ADC noise.
static int adc_fast = -1;

// Knob "double-max sweep" mode-change gesture state.
// 0 = idle, 1 = hit max once (waiting for it to fall away),
// 2 = fell away (armed, waiting for the second max hit).
static uint8_t knob_gesture_stage = 0;
static uint32_t knob_gesture_deadline = 0;

// When false, the physical pot is ignored and the web
// brightness slider is in control.
static volatile bool knob_enabled = true;

static uint32_t last_pan_time = 0;
static uint32_t last_move_time = 0;

static bool settings_dirty = false;

static bool center_prev = false;
static uint32_t center_press_time = 0;
static uint32_t center_release_time = 0;

static uint32_t last_status_print = 0;

// ============================================================
// Web -> main loop mailbox. HTTP handlers ONLY write these;
// the main loop is the only task that talks to the camera
// UART, so commands stay serialized and paced.
// ============================================================
typedef struct
{
    volatile bool dirty;
    volatile int  val;
} wp_t;

static volatile int  web_x = -1;
static volatile int  web_y = -1;
static volatile int  web_z = -1;
static volatile bool web_xyz_dirty = false;

static wp_t wp_bright;
static wp_t wp_contrast;
static wp_t wp_detail;
static wp_t wp_edge;
static wp_t wp_scene;
static wp_t wp_palette;
static wp_t wp_flip;
static wp_t wp_cross;

static volatile bool web_nuc_req = false;
static volatile bool web_bgc_req = false;
static volatile int  web_preset_req = -1;
static volatile bool web_preset_save_req = false;
static volatile bool web_center_req = false;
static volatile bool web_save_req = false;
static volatile bool web_camsave_req = false;

static uint32_t millis(void)
{
    return xTaskGetTickCount() * portTICK_PERIOD_MS;
}

static int clampi(int v, int lo, int hi)
{
    if(v < lo) return lo;
    if(v > hi) return hi;
    return v;
}

// ------------------------------------------------------------
// Debounced button reader
// ------------------------------------------------------------
typedef struct
{
    gpio_num_t pin;
    bool stable;
    bool last_raw;
    uint32_t last_edge;
} btn_t;

static btn_t btn_up     = { .pin = PIN_UP };
static btn_t btn_down   = { .pin = PIN_DOWN };
static btn_t btn_left   = { .pin = PIN_LEFT };
static btn_t btn_right  = { .pin = PIN_RIGHT };
static btn_t btn_center = { .pin = PIN_CENTER };

static void btn_update(btn_t *b, uint32_t now)
{
    bool raw = (gpio_get_level(b->pin) == 0);

    if(raw != b->last_raw)
    {
        b->last_edge = now;
        b->last_raw = raw;
    }

    if(raw != b->stable &&
       (now - b->last_edge) >= DEBOUNCE_MS)
    {
        b->stable = raw;
    }
}

static void buttons_update(uint32_t now)
{
    btn_update(&btn_up, now);
    btn_update(&btn_down, now);
    btn_update(&btn_left, now);
    btn_update(&btn_right, now);
    btn_update(&btn_center, now);
}

static bool dpad_allowed(uint32_t now)
{
    if(btn_center.stable)
        return false;

    if((now - center_release_time) < DPAD_LOCKOUT_MS)
        return false;

    return true;
}

// ------------------------------------------------------------
// NVS persistence: position, presets, active preset
// ------------------------------------------------------------
static void save_position(void)
{
    nvs_handle_t nvs;

    if(nvs_open("thermal", NVS_READWRITE, &nvs) == ESP_OK)
    {
        nvs_set_u16(nvs, "x", zoom_x);
        nvs_set_u16(nvs, "y", zoom_y);
        nvs_commit(nvs);
        nvs_close(nvs);
    }
}

static void save_presets(void)
{
    nvs_handle_t nvs;

    if(nvs_open("thermal", NVS_READWRITE, &nvs) == ESP_OK)
    {
        nvs_set_blob(nvs, "presets", presets, sizeof(presets));
        nvs_set_u8(nvs, "preset", active_preset);
        nvs_commit(nvs);
        nvs_close(nvs);
    }
}

static void load_settings(void)
{
    nvs_handle_t nvs;

    zoom_x = 128;
    zoom_y = 96;

    if(nvs_open("thermal", NVS_READONLY, &nvs) == ESP_OK)
    {
        nvs_get_u16(nvs, "x", &zoom_x);
        nvs_get_u16(nvs, "y", &zoom_y);

        size_t len = sizeof(presets);
        preset_t tmp[3];

        if(nvs_get_blob(nvs, "presets", tmp, &len) == ESP_OK &&
           len == sizeof(presets))
        {
            memcpy(presets, tmp, sizeof(presets));
        }

        uint8_t p = 0;
        if(nvs_get_u8(nvs, "preset", &p) == ESP_OK && p < 3)
            active_preset = p;

        nvs_close(nvs);
    }

    if(zoom_x < ALIGN_X_MIN) zoom_x = ALIGN_X_MIN;
    if(zoom_x > ALIGN_X_MAX) zoom_x = ALIGN_X_MAX;

    if(zoom_y < ALIGN_Y_MIN) zoom_y = ALIGN_Y_MIN;
    if(zoom_y > ALIGN_Y_MAX) zoom_y = ALIGN_Y_MAX;
}

static void send_point_zoom(void)
{
    Mini2_set_point_zoom(
        &cam,
        zoom_x,
        zoom_y,
        zoom_level);

    test_zoom = true;
}

static void next_zoom_level(void)
{
    zoom_level++;

    if(zoom_level > ZOOM_MAX)
        zoom_level = ZOOM_MIN;

    printf("\nZOOM = %.1fx\n", zoom_level / 10.0f);

    send_point_zoom();
}

static void center_alignment(void)
{
    zoom_x = ALIGN_CENTER_X;
    zoom_y = ALIGN_CENTER_Y;

    printf("\nCENTER ALIGNMENT\n");

    send_point_zoom();

    pan_count++;

    settings_dirty = true;
    last_move_time = millis();
}

static void apply_preset(void)
{
    preset_t *p = &presets[active_preset];

    // Sync live tuning state to the preset
    cur_palette  = p->pseudo_color;
    cur_scene    = p->scene_mode;
    cur_contrast = p->contrast;
    cur_edge     = p->edge;
    cur_detail   = p->detail;

    printf("\nAPPLY PRESET %u\n", active_preset);

    Mini2_set_color_pallet(&cam, cur_palette);
    vTaskDelay(pdMS_TO_TICKS(50));

    Mini2_set_scene_mode(&cam, cur_scene);
    vTaskDelay(pdMS_TO_TICKS(50));

    Mini2_set_contrast(&cam, cur_contrast);
    vTaskDelay(pdMS_TO_TICKS(50));

    Mini2_set_edge_enhancment(&cam, cur_edge);
    vTaskDelay(pdMS_TO_TICKS(50));

    Mini2_set_detail_enhancement(&cam, cur_detail);
    vTaskDelay(pdMS_TO_TICKS(50));

    printf("Preset applied\n");
}

static void next_preset(void)
{
    active_preset++;

    if(active_preset >= 3)
        active_preset = 0;

    mode_change_count++;

    printf("\nNEXT PRESET = %u\n",
           active_preset);

    apply_preset();

    test_mode = true;
}

static void setup_gpio(void)
{
    gpio_config_t io = {
        .mode = GPIO_MODE_INPUT,
        .pull_up_en = GPIO_PULLUP_ENABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE,
        .pin_bit_mask =
            (1ULL << PIN_CENTER) |
            (1ULL << PIN_LEFT)   |
            (1ULL << PIN_RIGHT)  |
            (1ULL << PIN_UP)     |
            (1ULL << PIN_DOWN)
    };

    gpio_config(&io);
}

static void setup_adc(void)
{
    adc1_config_width(ADC_WIDTH_BIT_12);
    adc1_config_channel_atten(
        ADC1_CHANNEL_4,
        ADC_ATTEN_DB_11);
}

// Watches the fast knob position for a quick max -> away -> max sweep
// and cycles the active preset when it sees one. Runs every pass (even
// when the web UI has taken over brightness) so the gesture state resets
// cleanly the moment "knob" control is handed back.
static void update_knob_gesture(int fast_raw)
{
    uint32_t now = millis();

    if(!knob_enabled)
    {
        knob_gesture_stage = 0;
        return;
    }

    if(knob_gesture_stage != 0 && now > knob_gesture_deadline)
        knob_gesture_stage = 0;   // took too long, gesture timed out

    switch(knob_gesture_stage)
    {
        case 0:   // idle, watching for the first max hit
            if(fast_raw <= KNOB_GESTURE_ENTER_RAW)
            {
                knob_gesture_stage = 1;
                knob_gesture_deadline = now + KNOB_GESTURE_WINDOW_MS;
            }
            break;

        case 1:   // hit max once, waiting to see it fall away
            if(fast_raw >= KNOB_GESTURE_EXIT_RAW)
            {
                knob_gesture_stage = 2;
                // Getting this far means we're mid-gesture -- give the
                // second hit the full window from right now rather than
                // eating into the time already spent on the first leg.
                knob_gesture_deadline = now + KNOB_GESTURE_WINDOW_MS;
            }
            break;

        case 2:   // armed, waiting for the second max hit
            if(fast_raw <= KNOB_GESTURE_ENTER_RAW)
            {
                knob_gesture_stage = 0;

                printf("\nKNOB DOUBLE-MAX SWEEP -> MODE CHANGE\n");

                next_preset();
            }
            break;
    }
}

static void update_brightness(void)
{
    int raw = adc1_get_raw(ADC1_CHANNEL_4);

    if(adc_filtered < 0)
        adc_filtered = raw;

    adc_filtered = (adc_filtered * 7 + raw) / 8;

    if(raw < adc_min) adc_min = raw;
    if(raw > adc_max) adc_max = raw;

    if(adc_fast < 0)
        adc_fast = raw;

    adc_fast = (adc_fast + raw) / 2;

    update_knob_gesture(adc_fast);

    // Web UI has taken over brightness control
    if(!knob_enabled)
        return;

    uint32_t now = millis();

    if(now - last_brightness_cmd < BRIGHT_MIN_INTERVAL_MS)
        return;

    // The pot is wired so that its raw ADC reading increases in the
    // opposite direction of the intended brightness travel. Invert
    // the filtered reading before mapping it to a 0-100% value.
    int adc_reversed = 4095 - adc_filtered;

    uint8_t b = (adc_reversed * 100) / 4095;

    if(abs((int)b - (int)last_brightness) >= BRIGHT_DEADBAND)
    {
        brightness = b;
        brightness_count++;

        printf("\nBRIGHTNESS CMD %u\n", brightness);

        Mini2_set_brightness(&cam, brightness);

        last_brightness = brightness;
        last_brightness_cmd = now;
        test_brightness = true;
    }
}

static void update_pan(void)
{
    uint32_t now = millis();

    if(!dpad_allowed(now))
        return;

    if(now - last_pan_time < PAN_REPEAT_MS)
        return;

    bool moved = false;

    if(btn_up.stable)
    {
        if(zoom_y > ALIGN_Y_MIN)
            zoom_y -= PAN_STEP;

        moved = true;
    }

    if(btn_down.stable)
    {
        if(zoom_y < ALIGN_Y_MAX)
            zoom_y += PAN_STEP;

        moved = true;
    }

    if(btn_left.stable)
    {
        if(zoom_x > ALIGN_X_MIN)
            zoom_x -= PAN_STEP;

        moved = true;
    }

    if(btn_right.stable)
    {
        if(zoom_x < ALIGN_X_MAX)
            zoom_x += PAN_STEP;

        moved = true;
    }

    if(!moved)
        return;

    zoom_x = clampi(zoom_x, ALIGN_X_MIN, ALIGN_X_MAX);
    zoom_y = clampi(zoom_y, ALIGN_Y_MIN, ALIGN_Y_MAX);

    pan_count++;

    printf("\nPAN CMD X=%u Y=%u Z=%.1fx\n",
           zoom_x,
           zoom_y,
           zoom_level / 10.0f);

    send_point_zoom();

    last_pan_time = now;
    last_move_time = now;
    settings_dirty = true;
}

static void update_center_button(void)
{
    bool current = btn_center.stable;
    uint32_t now = millis();

    if(current && !center_prev)
    {
        center_press_time = now;

        if(waiting_for_second_click &&
           (now - last_click_time) < DOUBLE_WINDOW_MS)
        {
            printf("DOUBLE CLICK\n");

            waiting_for_second_click = false;
            swallow_next_release = true;

            next_zoom_level();
        }
    }

    if(!current && center_prev)
    {
        center_release_time = now;

        uint32_t held = now - center_press_time;

        if(swallow_next_release)
        {
            swallow_next_release = false;
        }
        else if(held >= CENTER_PRESS_MS)
        {
            center_alignment();
        }
        else if(held >= NUC_PRESS_MS)
        {
            printf("\nNUC COMMAND\n");

            nuc_count++;

            Mini2_NUC(&cam);

            test_nuc = true;
        }
        else
        {
            waiting_for_second_click = true;
            last_click_time = now;
        }
    }

    if(waiting_for_second_click &&
       !current &&
       (now - last_click_time) >= DOUBLE_WINDOW_MS)
    {
        waiting_for_second_click = false;

        next_preset();
    }

    center_prev = current;
}

// ------------------------------------------------------------
// Apply pending web commands. Runs in the main loop.
// Tuning params are sent one per pass, min TUNE_REPEAT_MS
// apart, so slider drags can't flood the camera UART.
// ------------------------------------------------------------
static uint32_t last_tune_time = 0;

static void process_web_commands(void)
{
    uint32_t now = millis();

    // ---- Alignment (XY pad / sliders) ----
    if(web_xyz_dirty &&
       (now - last_pan_time >= PAN_REPEAT_MS))
    {
        int x = web_x;
        int y = web_y;
        int z = web_z;

        web_xyz_dirty = false;

        zoom_x = (uint16_t)clampi(x, ALIGN_X_MIN, ALIGN_X_MAX);
        zoom_y = (uint16_t)clampi(y, ALIGN_Y_MIN, ALIGN_Y_MAX);
        zoom_level = (uint8_t)clampi(z, ZOOM_MIN, ZOOM_MAX);

        pan_count++;

        send_point_zoom();

        last_pan_time = now;
        last_move_time = now;
        settings_dirty = true;
    }

    // ---- One-shot actions ----
    if(web_nuc_req)
    {
        web_nuc_req = false;

        printf("\nWEB NUC\n");

        nuc_count++;
        Mini2_NUC(&cam);
        test_nuc = true;
    }

    if(web_bgc_req)
    {
        web_bgc_req = false;

        printf("\nWEB BACKGROUND CORRECTION\n");

        Mini2_Background_Correction(&cam);
    }

    if(web_preset_req >= 0)
    {
        int p = web_preset_req;
        web_preset_req = -1;

        if(p < 3)
        {
            active_preset = (uint8_t)p;
            mode_change_count++;

            apply_preset();
            save_presets();   // persist active preset choice

            test_mode = true;
        }
    }

    if(web_preset_save_req)
    {
        web_preset_save_req = false;

        preset_t *p = &presets[active_preset];

        p->pseudo_color = cur_palette;
        p->scene_mode   = cur_scene;
        p->contrast     = cur_contrast;
        p->edge         = cur_edge;
        p->detail       = cur_detail;

        save_presets();

        printf("\nTUNING SAVED TO PRESET %u\n", active_preset);
    }

    if(web_center_req)
    {
        web_center_req = false;
        center_alignment();
    }

    if(web_save_req)
    {
        web_save_req = false;

        printf("\nWEB SAVE POSITION\n");

        save_position();
        settings_dirty = false;
    }

    if(web_camsave_req)
    {
        web_camsave_req = false;

        printf("\nCAMERA PARAMETERS SAVE\n");

        Mini2_parameters_save(&cam);
    }

    // ---- Live tuning: one param per pass, paced ----
    if(now - last_tune_time < TUNE_REPEAT_MS)
        return;

    if(wp_bright.dirty)
    {
        wp_bright.dirty = false;

        int v = clampi(wp_bright.val, 0, 100);

        brightness = (uint8_t)v;
        last_brightness = brightness;
        brightness_count++;

        Mini2_set_brightness(&cam, brightness);

        test_brightness = true;
        last_tune_time = now;
        return;
    }

    if(wp_contrast.dirty)
    {
        wp_contrast.dirty = false;

        cur_contrast = (uint8_t)clampi(wp_contrast.val, 0, 100);

        Mini2_set_contrast(&cam, cur_contrast);

        last_tune_time = now;
        return;
    }

    if(wp_detail.dirty)
    {
        wp_detail.dirty = false;

        cur_detail = (uint8_t)clampi(wp_detail.val, 0, 100);

        Mini2_set_detail_enhancement(&cam, cur_detail);

        last_tune_time = now;
        return;
    }

    if(wp_edge.dirty)
    {
        wp_edge.dirty = false;

        cur_edge = (uint8_t)clampi(wp_edge.val, 0, 2);

        Mini2_set_edge_enhancment(&cam, cur_edge);

        last_tune_time = now;
        return;
    }

    if(wp_scene.dirty)
    {
        wp_scene.dirty = false;

        int v = wp_scene.val;

        if(v == 0 || v == 1 || v == 2 || v == 3 ||
           v == 4 || v == 5 || v == 9)
        {
            cur_scene = (enum SceneMode)v;

            Mini2_set_scene_mode(&cam, cur_scene);

            mode_change_count++;
            test_mode = true;
        }

        last_tune_time = now;
        return;
    }

    if(wp_palette.dirty)
    {
        wp_palette.dirty = false;

        int v = wp_palette.val;

        if(v == WHOT || v == BHOT)
        {
            cur_palette = (enum PseudoColor)v;

            Mini2_set_color_pallet(&cam, cur_palette);
        }

        last_tune_time = now;
        return;
    }

    if(wp_flip.dirty)
    {
        wp_flip.dirty = false;

        cur_flip = (enum FlipMode)clampi(wp_flip.val, 0, 3);

        Mini2_set_flip_mode(&cam, cur_flip);

        last_tune_time = now;
        return;
    }

    if(wp_cross.dirty)
    {
        wp_cross.dirty = false;

        cur_cross = (wp_cross.val != 0);

        Mini2_set_crosshair(&cam, cur_cross);

        last_tune_time = now;
        return;
    }
}

static void save_if_needed(void)
{
    uint32_t now = millis();

    if(settings_dirty &&
       (now - last_move_time > SAVE_DELAY_MS))
    {
        save_position();
        settings_dirty = false;
    }
}

static void qc_buttons(void)
{
    if(btn_up.stable)     test_up = true;
    if(btn_down.stable)   test_down = true;
    if(btn_left.stable)   test_left = true;
    if(btn_right.stable)  test_right = true;
    if(btn_center.stable) test_center = true;
}

static void qc_dashboard(void)
{
    uint32_t now = millis();

    if(now - last_status_print < 1000)
        return;

    last_status_print = now;

    bool adc_pass =
        (adc_min < 500) &&
        (adc_max > 3500);

    bool overall =
        test_up &&
        test_down &&
        test_left &&
        test_right &&
        test_center &&
        adc_pass &&
        test_zoom &&
        test_mode &&
        test_nuc &&
        test_brightness;

    printf("\033[2J");
    printf("\033[H");

    printf("========================================\n");
    printf(" BCOTI REMIX QC TEST STATION\n");
    printf(" WebUI: http://192.168.4.1  (%s)\n", WIFI_AP_SSID);
    printf(" Uptime: %lus\n", (unsigned long)(now / 1000));
    printf("========================================\n\n");

    printf("BUTTON TESTS (latched - ever pressed since boot)\n");
    printf("----------------------------------------\n");
    printf("UP       : %s\n", test_up ? "PASS" : "FAIL");
    printf("DOWN     : %s\n", test_down ? "PASS" : "FAIL");
    printf("LEFT     : %s\n", test_left ? "PASS" : "FAIL");
    printf("RIGHT    : %s\n", test_right ? "PASS" : "FAIL");
    printf("CENTER   : %s\n", test_center ? "PASS" : "FAIL");

    printf("\nLIVE INPUT STATES (wiring verification - watch these\n");
    printf("update in real time as you press each button)\n");
    printf("----------------------------------------\n");
    printf("UP       : %s\n", btn_up.stable ? "PRESSED" : "open");
    printf("DOWN     : %s\n", btn_down.stable ? "PRESSED" : "open");
    printf("LEFT     : %s\n", btn_left.stable ? "PRESSED" : "open");
    printf("RIGHT    : %s\n", btn_right.stable ? "PRESSED" : "open");
    printf("CENTER   : %s\n", btn_center.stable ? "PRESSED" : "open");

    printf("\nADC TEST\n");
    printf("----------------------------------------\n");
    printf("RAW      : %d\n",
           adc1_get_raw(ADC1_CHANNEL_4));

    printf("FILTERED : %d\n", adc_filtered);
    printf("MIN      : %d\n", adc_min);
    printf("MAX      : %d\n", adc_max);
    printf("KNOB     : %s\n", knob_enabled ? "ACTIVE" : "WEB OVERRIDE");

    printf("SWEEP    : %s\n",
           adc_pass ? "PASS" : "FAIL");

    printf("GESTURE  : stage=%u adc_fast=%d (enter<=%d exit>=%d) %s\n",
           knob_gesture_stage,
           adc_fast,
           KNOB_GESTURE_ENTER_RAW,
           KNOB_GESTURE_EXIT_RAW,
           knob_gesture_stage == 0 ? "(idle)" :
           knob_gesture_stage == 1 ? "(hit max, waiting for it to fall away)" :
                                      "(armed - hit max again for mode change)");

    printf("\nCOMMAND COUNTERS\n");
    printf("----------------------------------------\n");

    printf("MODE CMDS   : %lu\n",
           (unsigned long)mode_change_count);

    printf("NUC CMDS    : %lu\n",
           (unsigned long)nuc_count);

    printf("PAN CMDS    : %lu\n",
           (unsigned long)pan_count);

    printf("BRIGHT CMDS : %lu\n",
           (unsigned long)brightness_count);

    printf("\nCAMERA TESTS\n");
    printf("----------------------------------------\n");

    printf("BRIGHT   : %s\n",
           test_brightness ? "PASS" : "FAIL");

    printf("ZOOM     : %s\n",
           test_zoom ? "PASS" : "FAIL");

    printf("MODE     : %s\n",
           test_mode ? "PASS" : "FAIL");

    printf("NUC      : %s\n",
           test_nuc ? "PASS" : "FAIL");

    printf("\nLIVE VALUES\n");
    printf("----------------------------------------\n");

    printf("X=%u Y=%u ZOOM=%.1fx\n",
           zoom_x, zoom_y, zoom_level / 10.0f);
    printf("BRIGHT=%u CONTRAST=%u DETAIL=%u EDGE=%u\n",
           brightness, cur_contrast, cur_detail, cur_edge);
    printf("SCENE=%d PALETTE=%d FLIP=%d PRESET=%u\n",
           cur_scene, cur_palette, cur_flip, active_preset);

    printf("\nOVERALL STATUS\n");
    printf("----------------------------------------\n");

    if(overall)
        printf("PASS\n");
    else
        printf("FAIL\n");
}

// ============================================================
// Web UI. Single-page HMI:
//  - XY drag pad + sliders for alignment
//  - live tuning sliders (brightness/contrast/detail)
//  - segmented controls (scene, palette, edge, flip)
//  - preset select + save, NUC, BGC, crosshair, knob override
//  - debug card: live button states + ADC readout for wiring checks
// The page polls /api/state; controls the user is touching
// are never overwritten by the poll.
// ============================================================
static const char index_html[] =
"<!DOCTYPE html><html><head>"
"<meta charset='utf-8'>"
"<meta name='viewport' content='width=device-width,initial-scale=1'>"
"<title>BCOTI Control</title>"
"<style>"
"*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}"
"body{font-family:system-ui,sans-serif;background:#0d0d0f;color:#eee;"
"margin:0 auto;padding:14px;max-width:540px}"
"h1{font-size:18px;margin:4px 0 14px;display:flex;"
"justify-content:space-between;align-items:center}"
"#conn{width:10px;height:10px;border-radius:50%;background:#555}"
"#conn.ok{background:#30d158}"
"h2{font-size:12px;text-transform:uppercase;letter-spacing:1px;"
"color:#888;margin:0 0 10px}"
".card{background:#1a1a1e;border-radius:14px;padding:14px;"
"margin-bottom:14px}"
"label{display:flex;justify-content:space-between;font-size:13px;"
"margin:10px 0 2px;color:#aaa}"
"label span{color:#fff;font-variant-numeric:tabular-nums}"
"input[type=range]{width:100%;height:34px;accent-color:#0a84ff;margin:0}"
"input[type=range]:disabled{opacity:.35}"
".seg{display:flex;gap:6px;flex-wrap:wrap;margin:6px 0 12px}"
".seg button{flex:1;min-width:64px}"
"button{padding:12px 6px;font-size:14px;border:0;border-radius:10px;"
"background:#2a2a2e;color:#fff}"
"button.on{background:#0a84ff}"
"button:active{filter:brightness(1.4)}"
"button.warn{background:#5c2b1a}"
".row{display:flex;gap:8px;flex-wrap:wrap;margin-top:6px}"
".row button{flex:1;min-width:90px}"
"#pad{position:relative;height:170px;background:#101014;"
"border:1px solid #333;border-radius:10px;margin-bottom:6px;"
"touch-action:none;overflow:hidden}"
"#ph{position:absolute;top:0;bottom:0;width:1px;background:#444}"
"#pv{position:absolute;left:0;right:0;height:1px;background:#444}"
"#pd{position:absolute;width:18px;height:18px;border-radius:50%;"
"background:#0a84ff;transform:translate(-50%,-50%);"
"box-shadow:0 0 10px #0a84ff}"
".stat{font-size:12px;color:#777;margin-top:4px;min-height:16px}"
".row button.ind{pointer-events:none}"
"</style></head><body>"

"<h1>BCOTI &middot; Mini2 256 <span id='conn'></span></h1>"

"<div class='card'><h2>Alignment</h2>"
"<div id='pad'><div id='ph'></div><div id='pv'></div><div id='pd'></div></div>"
"<label>X <span id='xv'>-</span></label>"
"<input type='range' id='x' step='1'>"
"<label>Y <span id='yv'>-</span></label>"
"<input type='range' id='y' step='1'>"
"<label>Zoom <span id='zv'>-</span></label>"
"<input type='range' id='z' step='1'>"
"<div class='row'>"
"<button id='bC'>Center</button>"
"<button id='bSP'>Save Position</button>"
"</div></div>"

"<div class='card'><h2>Image</h2>"
"<label>Brightness <span id='bv'>-</span></label>"
"<input type='range' id='b' min='0' max='100' step='1'>"
"<div class='row' style='margin-bottom:6px'>"
"<button id='knob'>Knob</button>"
"</div>"
"<label>Contrast <span id='cv'>-</span></label>"
"<input type='range' id='c' min='0' max='100' step='1'>"
"<label>Detail <span id='dv'>-</span></label>"
"<input type='range' id='d' min='0' max='100' step='1'>"
"<label>Edge enhancement</label>"
"<div class='seg' id='edge'></div>"
"<label>Scene mode</label>"
"<div class='seg' id='scene'></div>"
"<label>Palette</label>"
"<div class='seg' id='pal'></div>"
"</div>"

"<div class='card'><h2>Presets</h2>"
"<div class='seg' id='pre'></div>"
"<div class='row'>"
"<button id='bPS'>Save tuning to preset</button>"
"</div>"
"<div class='stat'>Preset buttons apply saved settings. "
"Tune above, then save into the active slot.</div>"
"</div>"

"<div class='card'><h2>Tools</h2>"
"<label>Flip</label>"
"<div class='seg' id='flip'></div>"
"<div class='row'>"
"<button id='chx'>Crosshair</button>"
"<button id='bB'>Bg Correct</button>"
"</div>"
"<div class='row'>"
"<button class='warn' id='bN'>NUC</button>"
"<button class='warn' id='bCS'>Save to Camera</button>"
"</div>"
"<div class='stat' id='stat'>connecting...</div>"
"</div>"

"<div class='card'><h2>Debug / Wiring Check</h2>"
"<div class='stat' style='margin-bottom:10px'>Press each button and sweep "
"the brightness pot end to end. The indicators and readouts below track "
"in real time so you can confirm every input is wired correctly.</div>"
"<div class='row'>"
"<button class='ind' id='dU'>UP</button>"
"<button class='ind' id='dD'>DOWN</button>"
"<button class='ind' id='dL'>LEFT</button>"
"<button class='ind' id='dR'>RIGHT</button>"
"<button class='ind' id='dCt'>CENTER</button>"
"</div>"
"<label>ADC raw <span id='adcraw'>-</span></label>"
"<label>ADC filtered (brightness) <span id='adcfilt'>-</span></label>"
"<label>ADC fast (gesture) <span id='adcfast'>-</span></label>"
"<label>ADC min / max (since boot) <span id='adcmm'>-</span></label>"
"<label>Knob gesture <span id='kgest'>-</span></label>"
"<div class='stat' style='margin-bottom:10px'>Turn the knob to max, let it "
"fall away, then hit max again quickly to cycle the mode.</div>"
"<label>Uptime <span id='uptime'>-</span></label>"
"<label>Cmd counts (mode / nuc / pan / bright) <span id='cnts'>-</span></label>"
"</div>"

"<script>"
"var S=null,hold={},qd={},qt=null,note_t=null;"
"function $(i){return document.getElementById(i)}"
"function touch(k){hold[k]=Date.now()}"
"function held(k){return hold[k]&&(Date.now()-hold[k])<1500}"
"function q(k,v){qd[k]=v;clearTimeout(qt);qt=setTimeout(flush,60)}"
"function flush(){var a=[];for(var k in qd)a.push(k+'='+qd[k]);qd={};"
"if(a.length)fetch('/api/tune?'+a.join('&'))}"
"function cmd(c){fetch('/api/'+c)}"
"function note(t){$('stat').textContent=t;clearTimeout(note_t);"
"note_t=setTimeout(function(){$('stat').textContent=''},2500)}"

"function lb(){$('xv').textContent=$('x').value;"
"$('yv').textContent=$('y').value;"
"$('zv').textContent=($('z').value/10).toFixed(1)+'x';"
"$('bv').textContent=$('b').value+'%';"
"$('cv').textContent=$('c').value;"
"$('dv').textContent=$('d').value}"

"function bindSlider(id,key){var e=$(id);"
"e.addEventListener('input',function(){touch(key);lb();q(key,e.value)});"
"e.addEventListener('pointerdown',function(){touch(key)})}"
"bindSlider('x','x');bindSlider('y','y');bindSlider('z','z');"
"bindSlider('b','bright');bindSlider('c','contrast');bindSlider('d','detail');"

"function seg(id,opts,key){var d=$(id);opts.forEach(function(o){"
"var b=document.createElement('button');b.textContent=o[1];"
"b.dataset.v=o[0];b.onclick=function(){touch(key);q(key,o[0]);"
"sel(id,o[0])};d.appendChild(b)})}"
"function sel(id,v){var c=$(id).children;for(var i=0;i<c.length;i++)"
"c[i].classList.toggle('on',c[i].dataset.v==v)}"
"function dind(id,v){$(id).classList.toggle('on',v==1)}"
"seg('edge',[[0,'Off'],[1,'Low'],[2,'High']],'edge');"
"seg('scene',[[0,'LowHL'],[1,'Linear'],[2,'LowCon'],[3,'General'],"
"[4,'HiCon'],[5,'Highlight'],[9,'Outline']],'scene');"
"seg('pal',[[0,'White hot'],[9,'Black hot']],'pal');"
"seg('flip',[[0,'None'],[1,'X'],[2,'Y'],[3,'XY']],'flip');"

"var pn=['P1','P2','P3'];pn.forEach(function(n,i){"
"var b=document.createElement('button');b.textContent=n;b.dataset.v=i;"
"b.onclick=function(){cmd('preset?n='+i);sel('pre',i);"
"note('applying preset '+n+'...');setTimeout(poll,800)};"
"$('pre').appendChild(b)});"

"var pad=$('pad');"
"function padmove(e){if(!S)return;"
"var r=pad.getBoundingClientRect();"
"var px=Math.min(1,Math.max(0,(e.clientX-r.left)/r.width));"
"var py=Math.min(1,Math.max(0,(e.clientY-r.top)/r.height));"
"var x=Math.round(S.xmin+px*(S.xmax-S.xmin));"
"var y=Math.round(S.ymin+py*(S.ymax-S.ymin));"
"$('x').value=x;$('y').value=y;lb();dot(x,y);"
"touch('x');touch('y');q('x',x);q('y',y)}"
"pad.addEventListener('pointerdown',function(e){"
"pad.setPointerCapture(e.pointerId);padmove(e);"
"pad.onpointermove=padmove});"
"pad.addEventListener('pointerup',function(){pad.onpointermove=null});"
"function dot(x,y){if(!S)return;"
"var px=(x-S.xmin)/(S.xmax-S.xmin)*100;"
"var py=(y-S.ymin)/(S.ymax-S.ymin)*100;"
"$('pd').style.left=px+'%';$('pd').style.top=py+'%';"
"$('ph').style.left=px+'%';$('pv').style.top=py+'%'}"

"$('bC').onclick=function(){cmd('center');note('centered');"
"setTimeout(poll,300)};"
"$('bSP').onclick=function(){cmd('save');note('position saved')};"
"$('bPS').onclick=function(){cmd('preset_save');"
"note('tuning saved to preset '+(S?S.preset+1:''))};"
"$('bN').onclick=function(){cmd('nuc');note('NUC sent')};"
"$('bB').onclick=function(){cmd('bgc');note('background correction sent')};"
"$('bCS').onclick=function(){"
"if(confirm('Save current parameters to camera flash?'))"
"{cmd('camsave');note('camera parameters saved')}};"
"$('chx').onclick=function(){touch('cross');"
"var v=$('chx').classList.contains('on')?0:1;"
"$('chx').classList.toggle('on',v==1);q('cross',v)};"
"$('knob').onclick=function(){touch('knob');"
"var v=$('knob').classList.contains('on')?0:1;"
"setKnob(v);q('knob',v)};"
"function setKnob(v){$('knob').classList.toggle('on',v==1);"
"$('knob').textContent=v==1?'Knob active':'Knob off (web)';"
"$('b').disabled=(v==1)}"

"function apply(s){S=s;$('conn').classList.add('ok');"
"function st(id,key,v){if(!held(key)){$(id).value=v}}"
"$('x').min=s.xmin;$('x').max=s.xmax;"
"$('y').min=s.ymin;$('y').max=s.ymax;"
"$('z').min=s.zmin;$('z').max=s.zmax;"
"st('x','x',s.x);st('y','y',s.y);st('z','z',s.z);"
"st('b','bright',s.bright);st('c','contrast',s.contrast);"
"st('d','detail',s.detail);"
"if(!held('edge'))sel('edge',s.edge);"
"if(!held('scene'))sel('scene',s.scene);"
"if(!held('pal'))sel('pal',s.pal);"
"if(!held('flip'))sel('flip',s.flip);"
"if(!held('cross'))$('chx').classList.toggle('on',s.cross==1);"
"if(!held('knob'))setKnob(s.knob);"
"sel('pre',s.preset);"
"if(!held('x')&&!held('y'))dot(s.x,s.y);"
"if(s.dbg){"
"dind('dU',s.dbg.up);dind('dD',s.dbg.down);dind('dL',s.dbg.left);"
"dind('dR',s.dbg.right);dind('dCt',s.dbg.center);"
"$('adcraw').textContent=s.dbg.adc_raw;"
"$('adcfilt').textContent=s.dbg.adc_filt;"
"$('adcfast').textContent=s.dbg.adc_fast;"
"$('adcmm').textContent=s.dbg.adc_min+' / '+s.dbg.adc_max;"
"$('kgest').textContent=["
"'idle','armed (fell away from max)','ready (hit max = mode change)'"
"][s.dbg.knob_stage]||s.dbg.knob_stage;"
"$('uptime').textContent=(s.dbg.uptime/1000).toFixed(1)+'s';"
"$('cnts').textContent=s.dbg.cnt_mode+' / '+s.dbg.cnt_nuc+' / '+"
"s.dbg.cnt_pan+' / '+s.dbg.cnt_bright}"
"lb()}"

"function poll(){fetch('/api/state')"
".then(function(r){return r.json()}).then(apply)"
".catch(function(){$('conn').classList.remove('ok')})}"
"poll();setInterval(poll,1000);"
"</script></body></html>";

// ------------------------------------------------------------
// HTTP handlers
// ------------------------------------------------------------
static esp_err_t root_get_handler(httpd_req_t *req)
{
    httpd_resp_set_type(req, "text/html");
    return httpd_resp_send(req, index_html, HTTPD_RESP_USE_STRLEN);
}

static bool qint(const char *query, const char *key, int *out)
{
    char val[16];

    if(httpd_query_key_value(query, key, val, sizeof(val)) == ESP_OK)
    {
        *out = atoi(val);
        return true;
    }

    return false;
}

static esp_err_t api_state_handler(httpd_req_t *req)
{
    char json[768];

    int adc_raw_now = adc1_get_raw(ADC1_CHANNEL_4);

    snprintf(json, sizeof(json),
        "{\"x\":%u,\"y\":%u,\"z\":%u,"
        "\"xmin\":%d,\"xmax\":%d,"
        "\"ymin\":%d,\"ymax\":%d,"
        "\"zmin\":%d,\"zmax\":%d,"
        "\"bright\":%u,\"contrast\":%u,\"detail\":%u,\"edge\":%u,"
        "\"scene\":%d,\"pal\":%d,\"flip\":%d,\"cross\":%d,"
        "\"knob\":%d,\"preset\":%u,\"pan\":%lu,"
        "\"dbg\":{"
        "\"up\":%d,\"down\":%d,\"left\":%d,\"right\":%d,\"center\":%d,"
        "\"adc_raw\":%d,\"adc_filt\":%d,\"adc_fast\":%d,"
        "\"adc_min\":%d,\"adc_max\":%d,"
        "\"knob_stage\":%u,"
        "\"uptime\":%lu,"
        "\"cnt_mode\":%lu,\"cnt_nuc\":%lu,\"cnt_pan\":%lu,\"cnt_bright\":%lu"
        "}}",
        zoom_x, zoom_y, zoom_level,
        ALIGN_X_MIN, ALIGN_X_MAX,
        ALIGN_Y_MIN, ALIGN_Y_MAX,
        ZOOM_MIN, ZOOM_MAX,
        brightness, cur_contrast, cur_detail, cur_edge,
        (int)cur_scene, (int)cur_palette, (int)cur_flip,
        cur_cross ? 1 : 0,
        knob_enabled ? 1 : 0,
        active_preset,
        (unsigned long)pan_count,
        btn_up.stable ? 1 : 0,
        btn_down.stable ? 1 : 0,
        btn_left.stable ? 1 : 0,
        btn_right.stable ? 1 : 0,
        btn_center.stable ? 1 : 0,
        adc_raw_now,
        adc_filtered,
        adc_fast,
        adc_min,
        adc_max,
        knob_gesture_stage,
        (unsigned long)millis(),
        (unsigned long)mode_change_count,
        (unsigned long)nuc_count,
        (unsigned long)pan_count,
        (unsigned long)brightness_count);

    httpd_resp_set_type(req, "application/json");
    return httpd_resp_send(req, json, HTTPD_RESP_USE_STRLEN);
}

static esp_err_t api_tune_handler(httpd_req_t *req)
{
    char query[256];
    int v;

    if(httpd_req_get_url_query_str(req, query, sizeof(query)) == ESP_OK)
    {
        // Alignment
        bool xyz = false;

        int x = zoom_x, y = zoom_y, z = zoom_level;

        if(qint(query, "x", &v)) { x = v; xyz = true; }
        if(qint(query, "y", &v)) { y = v; xyz = true; }
        if(qint(query, "z", &v)) { z = v; xyz = true; }

        if(xyz)
        {
            web_x = x;
            web_y = y;
            web_z = z;
            web_xyz_dirty = true;
        }

        // Tuning
        if(qint(query, "bright", &v))
        {
            wp_bright.val = v;
            wp_bright.dirty = true;
        }

        if(qint(query, "contrast", &v))
        {
            wp_contrast.val = v;
            wp_contrast.dirty = true;
        }

        if(qint(query, "detail", &v))
        {
            wp_detail.val = v;
            wp_detail.dirty = true;
        }

        if(qint(query, "edge", &v))
        {
            wp_edge.val = v;
            wp_edge.dirty = true;
        }

        if(qint(query, "scene", &v))
        {
            wp_scene.val = v;
            wp_scene.dirty = true;
        }

        if(qint(query, "pal", &v))
        {
            wp_palette.val = v;
            wp_palette.dirty = true;
        }

        if(qint(query, "flip", &v))
        {
            wp_flip.val = v;
            wp_flip.dirty = true;
        }

        if(qint(query, "cross", &v))
        {
            wp_cross.val = v;
            wp_cross.dirty = true;
        }

        if(qint(query, "knob", &v))
        {
            knob_enabled = (v != 0);
        }
    }

    return httpd_resp_send(req, "ok", HTTPD_RESP_USE_STRLEN);
}

static esp_err_t api_nuc_handler(httpd_req_t *req)
{
    web_nuc_req = true;
    return httpd_resp_send(req, "ok", HTTPD_RESP_USE_STRLEN);
}

static esp_err_t api_bgc_handler(httpd_req_t *req)
{
    web_bgc_req = true;
    return httpd_resp_send(req, "ok", HTTPD_RESP_USE_STRLEN);
}

static esp_err_t api_preset_handler(httpd_req_t *req)
{
    char query[64];
    int n;

    if(httpd_req_get_url_query_str(req, query, sizeof(query)) == ESP_OK &&
       qint(query, "n", &n) &&
       n >= 0 && n < 3)
    {
        web_preset_req = n;
    }

    return httpd_resp_send(req, "ok", HTTPD_RESP_USE_STRLEN);
}

static esp_err_t api_preset_save_handler(httpd_req_t *req)
{
    web_preset_save_req = true;
    return httpd_resp_send(req, "ok", HTTPD_RESP_USE_STRLEN);
}

static esp_err_t api_center_handler(httpd_req_t *req)
{
    web_center_req = true;
    return httpd_resp_send(req, "ok", HTTPD_RESP_USE_STRLEN);
}

static esp_err_t api_save_handler(httpd_req_t *req)
{
    web_save_req = true;
    return httpd_resp_send(req, "ok", HTTPD_RESP_USE_STRLEN);
}

static esp_err_t api_camsave_handler(httpd_req_t *req)
{
    web_camsave_req = true;
    return httpd_resp_send(req, "ok", HTTPD_RESP_USE_STRLEN);
}

static void start_webserver(void)
{
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    config.lru_purge_enable = true;
    config.max_uri_handlers = 12;

    httpd_handle_t server = NULL;

    if(httpd_start(&server, &config) != ESP_OK)
    {
        printf("Failed to start HTTP server\n");
        return;
    }

    const httpd_uri_t uris[] = {
        { .uri = "/",                .method = HTTP_GET, .handler = root_get_handler },
        { .uri = "/api/state",       .method = HTTP_GET, .handler = api_state_handler },
        { .uri = "/api/tune",        .method = HTTP_GET, .handler = api_tune_handler },
        { .uri = "/api/nuc",         .method = HTTP_GET, .handler = api_nuc_handler },
        { .uri = "/api/bgc",         .method = HTTP_GET, .handler = api_bgc_handler },
        { .uri = "/api/preset",      .method = HTTP_GET, .handler = api_preset_handler },
        { .uri = "/api/preset_save", .method = HTTP_GET, .handler = api_preset_save_handler },
        { .uri = "/api/center",      .method = HTTP_GET, .handler = api_center_handler },
        { .uri = "/api/save",        .method = HTTP_GET, .handler = api_save_handler },
        { .uri = "/api/camsave",     .method = HTTP_GET, .handler = api_camsave_handler },
    };

    for(int i = 0; i < sizeof(uris) / sizeof(uris[0]); i++)
        httpd_register_uri_handler(server, &uris[i]);
}

static void wifi_init_softap(void)
{
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    esp_netif_create_default_wifi_ap();

    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));

    wifi_config_t wifi_config = {
        .ap = {
            .ssid = WIFI_AP_SSID,
            .password = WIFI_AP_PASS,
            .channel = WIFI_AP_CHANNEL,
            .max_connection = WIFI_AP_MAX_CONN,
            .authmode = WIFI_AUTH_WPA2_PSK,
        },
    };

    ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_AP));
    ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &wifi_config));
    ESP_ERROR_CHECK(esp_wifi_start());

    printf("WiFi AP '%s' started, UI at http://192.168.4.1\n",
           WIFI_AP_SSID);
}

void app_main(void)
{
    esp_err_t ret = nvs_flash_init();

    if(ret == ESP_ERR_NVS_NO_FREE_PAGES ||
       ret == ESP_ERR_NVS_NEW_VERSION_FOUND)
    {
        nvs_flash_erase();
        nvs_flash_init();
    }

    setup_gpio();
    setup_adc();

    load_settings();

    wifi_init_softap();
    start_webserver();

    cam.uart_port = UART_NUM_1;
    cam.uart_tx   = PIN_UART_TX;
    cam.uart_rx   = PIN_UART_RX;
    cam.variant   = (Mini2_variant_t)Mini2_256;

    vTaskDelay(pdMS_TO_TICKS(5000));

    Mini2_init(&cam);

    vTaskDelay(pdMS_TO_TICKS(1000));

    printf("Applying startup mode...\n");

    apply_preset();

    vTaskDelay(pdMS_TO_TICKS(500));

    printf("Applying startup brightness...\n");

    update_brightness();

    vTaskDelay(pdMS_TO_TICKS(500));

    printf("Applying startup zoom...\n");

    Mini2_set_centre_zoom(&cam, 10);

    vTaskDelay(pdMS_TO_TICKS(250));

    for(int i = 0; i < 3; i++)
    {
        send_point_zoom();
        vTaskDelay(pdMS_TO_TICKS(50));
    }

    while(1)
    {
        uint32_t now = millis();

        buttons_update(now);

        qc_buttons();

        update_pan();
        update_center_button();
        update_brightness();
        process_web_commands();
        save_if_needed();

        qc_dashboard();

        vTaskDelay(pdMS_TO_TICKS(10));
    }
}