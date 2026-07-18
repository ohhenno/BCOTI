idf_component_register(SRCS "main.c" "Mini2.c"
                       INCLUDE_DIRS "."
                       REQUIRES driver nvs_flash esp_wifi esp_http_server esp_netif esp_event)