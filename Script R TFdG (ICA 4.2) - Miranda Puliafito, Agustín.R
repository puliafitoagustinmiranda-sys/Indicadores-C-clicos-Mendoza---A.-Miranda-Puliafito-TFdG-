# ==============================================================================
# SCRIPT MAESTRO: PROXIES, ICS, ICA E ÍNDICE DE DIFUSIÓN
# Autor: Agustín Miranda Puliafito | Universidad Nacional de Cuyo
# ==============================================================================

# ------------------------------------------------------------------------------
# 0. CONFIGURACIÓN INICIAL Y LIBRERÍAS
# ------------------------------------------------------------------------------

library(readxl)
library(dplyr)
library(tidyr)
library(lubridate)
library(forecast)
library(tempdisagg)
library(tsbox)
library(seasonal)
library(mFilter)
library(zoo)
library(lmtest)
library(ggplot2)
library(patchwork)
library(knitr)
library(tsibble)
library(feasts)
library(fable)
library(purrr)
library(showtext)

options(scipen = 999)
setwd("C:/Users/paola/OneDrive/Documentos/Agustin/Facultad/Tesis/R - BdD")

ruta_proxies <- "01 - Proxies base de datos.xlsx"
ruta_ica     <- "02 - ICA base de datos.xlsx"

lambda_hp_mensual <- 14400
lambda_hp_anual   <- 100

col_ics <- "#003366"  # Azul Marino
col_ica <- "#E69F00"  # Naranja
col_pbg <- "#17becf"  # Turquesa

meses_num <- c(
  "enero" = 1, "febrero" = 2, "marzo" = 3, "abril" = 4,
  "mayo" = 5, "junio" = 6, "julio" = 7, "agosto" = 8,
  "septiembre" = 9, "octubre" = 10, "noviembre" = 11, "diciembre" = 12,
  "ene" = 1, "feb" = 2, "mar" = 3, "abr" = 4, "may" = 5, "jun" = 6,
  "jul" = 7, "ago" = 8, "sep" = 9, "oct" = 10, "nov" = 11, "dic" = 12
)

# ------------------------------------------------------------------------------
# FUNCIONES AUXILIARES GENERALES
# Asumen como estándar la columna 'fecha' en minúscula
# ------------------------------------------------------------------------------

# 1. Variación Porcentual Simétrica
calc_variacion_simetrica <- function(x) {
  n <- length(x)
  if (n < 2) return(rep(NA_real_, n))
  c(NA_real_, 200 * (diff(x) / (x[-n] + x[-1])))
}

# 1.b Tasa de Variación Interanual (TVI) 
calc_tvi <- function(x) {
  100 * (x - dplyr::lag(x)) / dplyr::lag(x)
}

# ==============================================================================
# 2. ALGORITMO Y GRÁFICOS BRY-BOSCHAN (BLOQUE COMPLETO UNIFICADO)
# ==============================================================================

# 2.1 Algoritmo Bry-Boschan NBER
bry_boschan_nber <- function(df_datos, col_y, k = 5, min_phase = 6, min_cycle = 15) {
  
  df_cln <- df_datos[!is.na(df_datos[[col_y]]), ]
  if(nrow(df_cln) < min_cycle) return(data.frame()) 
  
  y_orig <- as.numeric(df_cln[[col_y]])
  n <- length(y_orig)
  vec_fechas <- df_cln$fecha
  
  y_suave <- as.numeric(stats::filter(y_orig, rep(1/5, 5), sides = 2))
  idx_na <- is.na(y_suave)
  y_suave[idx_na] <- y_orig[idx_na] 
  
  limpiar_alternancia <- function(idx, type, y_vals) {
    changed <- TRUE
    while (changed) {
      changed <- FALSE
      if (length(idx) < 2) break
      for (j in 1:(length(idx) - 1)) {
        if (type[j] == type[j + 1]) {
          idx1 <- idx[j]; idx2 <- idx[j + 1]
          drop_idx <- if (type[j] == "Peak") ifelse(y_vals[idx1] < y_vals[idx2], j, j + 1) else ifelse(y_vals[idx1] > y_vals[idx2], j, j + 1)
          idx <- idx[-drop_idx]; type <- type[-drop_idx]
          changed <- TRUE; break
        }
      }
    }
    return(list(idx = idx, type = type))
  }
  
  aplicar_reglas_bb <- function(idx, type, y_vals) {
    res_alt <- limpiar_alternancia(idx, type, y_vals)
    idx <- res_alt$idx; type <- res_alt$type
    changed <- TRUE
    while (changed) {
      changed <- FALSE
      if (length(idx) < 2) break
      duraciones_fase <- diff(idx)
      fases_cortas <- which(duraciones_fase < min_phase)
      if (length(fases_cortas) > 0) {
        j <- fases_cortas[1]
        idx <- idx[-c(j, j + 1)]; type <- type[-c(j, j + 1)]
        res_alt <- limpiar_alternancia(idx, type, y_vals)
        idx <- res_alt$idx; type <- res_alt$type
        changed <- TRUE; next
      }
      if (length(idx) >= 3) {
        duraciones_ciclo <- diff(idx, lag = 2)
        ciclos_cortos <- which(duraciones_ciclo < min_cycle)
        if (length(ciclos_cortos) > 0) {
          j <- ciclos_cortos[1]
          idx_p1 <- idx[j]; idx_p3 <- idx[j + 2]
          drop_pos <- if (type[j] == "Peak") ifelse(y_vals[idx_p1] < y_vals[idx_p3], j, j + 2) else ifelse(y_vals[idx_p1] > y_vals[idx_p3], j, j + 2)
          idx <- idx[-drop_pos]; type <- type[-drop_pos]
          res_alt <- limpiar_alternancia(idx, type, y_vals)
          idx <- res_alt$idx; type <- res_alt$type
          changed <- TRUE
        }
      }
    }
    return(list(idx = idx, type = type))
  }
  
  peaks <- rep(FALSE, n)
  troughs <- rep(FALSE, n)
  
  inicio_busqueda <- max(k + 1, 7)
  fin_busqueda    <- min(n - k, n - 6)
  if(inicio_busqueda > fin_busqueda) return(data.frame())
  
  for (i in inicio_busqueda:fin_busqueda) {
    if (isTRUE(all(y_suave[i] > y_suave[(i - k):(i - 1)])) && isTRUE(all(y_suave[i] >= y_suave[(i + 1):(i + k)]))) peaks[i] <- TRUE
    if (isTRUE(all(y_suave[i] < y_suave[(i - k):(i - 1)])) && isTRUE(all(y_suave[i] <= y_suave[(i + 1):(i + k)]))) troughs[i] <- TRUE
  }
  
  tp_index_suave <- which(peaks | troughs)
  if (length(tp_index_suave) == 0) return(data.frame())
  tp_type_suave <- ifelse(peaks[tp_index_suave], "Peak", "Trough")
  
  res_tentativos <- aplicar_reglas_bb(tp_index_suave, tp_type_suave, y_suave)
  idx_tent <- res_tentativos$idx; type_tent <- res_tentativos$type
  if(length(idx_tent) == 0) return(data.frame())
  
  relocated_idx <- numeric(length(idx_tent))
  for (j in seq_along(idx_tent)) {
    punto <- idx_tent[j]; tipo <- type_tent[j]
    w_start <- max(1, punto - 5)
    w_end   <- min(n, punto + 5)
    
    segmento <- y_orig[w_start:w_end]
    if (length(segmento) == 0 || all(is.na(segmento))) {
      relocated_idx[j] <- punto 
    } else {
      relocated_idx[j] <- if(tipo == "Peak") w_start - 1 + which.max(segmento) else w_start - 1 + which.min(segmento)
    }
  }
  
  valid_bounds <- relocated_idx >= 7 & relocated_idx <= (n - 6)
  idx_final <- relocated_idx[valid_bounds]
  type_final <- type_tent[valid_bounds]
  
  if (length(idx_final) == 0) return(data.frame())
  res_final <- aplicar_reglas_bb(idx_final, type_final, y_orig)
  
  data.frame(fecha = vec_fechas[res_final$idx], Tipo = res_final$type, Valor = y_orig[res_final$idx])
}

# 2.2 Auditoría de Tiempos Bry-Boschan
auditar_tiempos_bb <- function(df_pg, df_serie = NULL) {
  if (is.null(df_pg) || nrow(df_pg) < 2) return(NULL)
  
  fecha_inicio <- NA
  if (!is.null(df_serie)) fecha_inicio <- min(df_serie$fecha, na.rm = TRUE)
  
  df_audit <- df_pg %>%
    rename(Fecha_Eval = fecha) %>%
    arrange(Fecha_Eval) %>%
    mutate(
      Giro  = ifelse(Tipo == "Peak", "Pico", "Valle"),
      Nivel = round(Valor, 2),
      
      `Duración fase (m)` = (year(Fecha_Eval) - year(dplyr::lag(Fecha_Eval, 1))) * 12 + 
        (month(Fecha_Eval) - month(dplyr::lag(Fecha_Eval, 1))),
      
      `Duración ciclo (m)` = (year(Fecha_Eval) - year(dplyr::lag(Fecha_Eval, 2))) * 12 + 
        (month(Fecha_Eval) - month(dplyr::lag(Fecha_Eval, 2))),
      
      Meses_Desde_Inicio = if(!is.na(fecha_inicio)) {
        (year(Fecha_Eval) - year(fecha_inicio)) * 12 + (month(Fecha_Eval) - month(fecha_inicio))
      } else { NA }
    ) %>%
    mutate(
      `Fase >= 6m` = case_when(
        !is.na(`Duración fase (m)`) & `Duración fase (m)` >= 6 ~ "Verdadero",
        !is.na(`Duración fase (m)`) & `Duración fase (m)` < 6  ~ "Falso",
        is.na(`Duración fase (m)`) & !is.na(Meses_Desde_Inicio) & Meses_Desde_Inicio >= 6 ~ "Verdadero",
        TRUE ~ "NA"
      ),
      `Ciclo >= 15m` = case_when(
        is.na(`Duración ciclo (m)`) ~ "NA",
        `Duración ciclo (m)` >= 15  ~ "Verdadero",
        TRUE                        ~ "Falso"
      )
    ) %>%
    rename(fecha = Fecha_Eval) %>%
    select(fecha, Giro, Nivel, `Duración fase (m)`, `Fase >= 6m`, `Duración ciclo (m)`, `Ciclo >= 15m`)
  
  return(df_audit)
}

# 2.3 Gráficos PdG
preparar_pg_plot <- function(df_datos, df_pg) {
  if (nrow(df_pg) == 0) {
    df_datos$Tipo_PG <- factor(NA, levels = c("Pico", "Valle"))
    return(df_datos)
  }
  df_datos %>%
    left_join(df_pg %>% select(fecha, Tipo, Valor), by = "fecha") %>%
    mutate(Tipo_PG = factor(Tipo, levels = c("Peak", "Trough"), labels = c("Pico", "Valle")))
}

# 2.4 Función Unificada para Gráficos Bry-Boschan
graficar_bry_boschan <- function(df_plot, col_tc_orig, col_tc_hp, titulo_serie, y_label, 
                                 es_moneda = FALSE, es_entero = FALSE, color_serie = "#003366") {
  
  p <- ggplot(df_plot, aes(x = fecha)) +
    geom_line(aes(y = .data[[col_tc_hp]], color = "TC filtro HP"), linewidth = 1.2) +
    geom_line(aes(y = .data[[col_tc_orig]], color = "TC original"), linewidth = 0.7, alpha = 0.85) +
    geom_point(
      data = filter(df_plot, !is.na(Tipo_PG)), 
      aes(y = Valor, color = as.character(Tipo_PG), shape = as.character(Tipo_PG)), 
      size = 3.5
    ) +
    scale_x_date(
      date_breaks = "2 years", 
      date_labels = "%Y", 
      limits = c(min(df_plot$fecha, na.rm = TRUE), max(df_plot$fecha, na.rm = TRUE)), 
      expand = c(0, 0)
    ) +
    coord_cartesian(clip = "off") +
    scale_color_manual(
      name = NULL,
      values = c(
        "TC filtro HP" = color_serie, 
        "TC original"  = "gray65",    
        "Pico"         = "red",       
        "Valle"        = "green4"
      ),
      breaks = c("TC filtro HP", "TC original", "Pico", "Valle")
    ) +
    scale_shape_manual(
      name = NULL,
      values = c(
        "TC filtro HP" = NA, 
        "TC original"  = NA, 
        "Pico"         = 17, 
        "Valle"        = 25
      ),
      breaks = c("TC filtro HP", "TC original", "Pico", "Valle")
    ) +
    guides(
      color = guide_legend(override.aes = list(
        linetype  = c("solid", "solid", "blank", "blank"),
        shape     = c(NA, NA, 17, 25),
        linewidth = c(1.2, 0.7, NA, NA)
      )),
      shape = "none"
    ) +
    labs(
      title = NULL,
      subtitle = NULL,
      x = NULL, y = y_label
    ) +
    theme_minimal(base_size = 10, base_family = "sans") + 
    theme(
      plot.title      = element_text(face = "bold", hjust = 0.5), 
      plot.subtitle   = element_text(hjust = 0.5, color = "grey30"),
      legend.position = "bottom",
      panel.border    = element_rect(color = "black", fill = NA, linewidth = 0.5), 
      axis.ticks      = element_line(color = "black", linewidth = 0.5), 
      axis.ticks.length = unit(0.15, "cm"),
      plot.margin     = margin(t = 10, r = 15, b = 10, l = 15)
    )
  
  if (es_moneda) {
    p <- p + scale_y_continuous(labels = scales::label_number(scale = 1e-6, suffix = " M", big.mark = "."))
  } else if (es_entero) {
    p <- p + scale_y_continuous(labels = scales::comma)
  }
  
  return(p)
}

# ==============================================================================
# 1. PBG Y MACROECONOMÍA DE REFERENCIA
# ==============================================================================

df_pbg_raw <- read_excel(ruta_proxies, sheet = "PBG")
df_pbg_compl_raw <- read_excel(ruta_proxies, sheet = "PBG completo")

# PBG Recortado (2010-2024)
df_pbg <- df_pbg_raw %>%
  rename(año = 1, pbg_2010 = 2) %>%
  mutate(año = as.numeric(año), pbg_2010 = as.numeric(pbg_2010)) %>%
  filter(!is.na(año) & año >= 2010 & año <= 2024) %>%
  arrange(año)

if (!2010 %in% df_pbg$año) {
  df_pbg <- bind_rows(data.frame(año = 2010, pbg_2010 = 100.0), df_pbg)
}

df_pbg <- df_pbg %>% mutate(tvi_pbg = calc_tvi(pbg_2010))

# PBG Completo (2004-2025)
df_pbg_compl <- df_pbg_compl_raw %>%
  rename(año = 1, pbg_compl = 2) %>%
  mutate(
    año = as.numeric(gsub("\\.", "", as.character(año))),
    pbg_compl = as.numeric(gsub(",", ".", as.character(pbg_compl)))
  ) %>%
  filter(!is.na(año))

df_pbg_comp_series <- full_join(df_pbg_compl, df_pbg, by = "año") %>% 
  arrange(año)

factor_escala_pbg <- max(df_pbg_comp_series$pbg_compl, na.rm = TRUE) / max(df_pbg_comp_series$pbg_2010, na.rm = TRUE)

plot_pbg_comparacion <- ggplot(df_pbg_comp_series, aes(x = año)) +
  geom_line(aes(y = pbg_compl, color = "PBG Serie Histórica (2004-2025)"), linewidth = 1, alpha = 0.45) +
  geom_line(aes(y = pbg_2010 * factor_escala_pbg, color = "PBG Base 2010 (2010-2024)"), linewidth = 1.2) +
  scale_x_continuous(breaks = seq(2004, 2025, by = 2), limits = c(min(df_pbg_comp_series$año, na.rm=TRUE), max(df_pbg_comp_series$año, na.rm=TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  scale_y_continuous(
    name = "Miles de pesos (Base 2004)",
    labels = scales::comma,
    sec.axis = sec_axis(~ . / factor_escala_pbg, name = "Índice (Base 2010 = 100)")
  ) +
  scale_color_manual(
    name = "Serie",
    values = c(
      "PBG Serie Histórica (2004-2025)" = "#9ECAE1",
      "PBG Base 2010 (2010-2024)" = col_pbg
    )
  ) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", size = 11, hjust = 0.5),
    plot.subtitle = element_text(size = 9.5, hjust = 0.5),
    axis.title = element_text(size = 9),
    axis.text = element_text(size = 8.5),
    legend.text = element_text(size = 9),
    legend.position = "bottom",
    panel.grid.minor = element_blank(),
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
    axis.ticks = element_line(color = "black", linewidth = 0.5),
    axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_pbg_comparacion)

plot_pbg_indiv <- ggplot(df_pbg, aes(x = año, y = pbg_2010)) +
  geom_line(color = col_pbg, linewidth = 1.2) +
  scale_x_continuous(breaks = seq(2010, 2024, by = 2), limits = c(min(df_pbg$año, na.rm = TRUE), max(df_pbg$año, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  scale_y_continuous(labels = scales::comma) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "Precios constantes (Base 2010 = 100)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", size = 11, hjust = 0.5),
    plot.subtitle = element_text(size = 9.5, hjust = 0.5),
    panel.grid.minor = element_blank(),
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
    axis.ticks = element_line(color = "black", linewidth = 0.5),
    axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_pbg_indiv)

pbg_ts <- ts(df_pbg$pbg_2010, start = 2010, frequency = 1)
hp_pbg <- hpfilter(pbg_ts, freq = lambda_hp_anual, type = "lambda")
df_pbg$pbg_suave_hp <- as.numeric(hp_pbg$trend)

plot_pbg_suave <- ggplot(df_pbg, aes(x = año)) +
  geom_line(aes(y = pbg_2010, color = "PBG Observado (Base 2010)"), linewidth = 1, linetype = "dashed") +
  geom_line(aes(y = pbg_suave_hp, color = "PBG Suavizado (Filtro HP)"), linewidth = 1.3, linetype = "solid") +
  scale_x_continuous(breaks = seq(2010, 2024, by = 2), limits = c(min(df_pbg$año, na.rm = TRUE), max(df_pbg$año, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  scale_y_continuous(labels = scales::comma) +
  scale_color_manual(
    name = "Serie",
    values = c("PBG Observado (Base 2010)" = col_pbg, "PBG Suavizado (Filtro HP)" = col_ics)
  ) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "Precios constantes (Base 2010 = 100)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", size = 11, hjust = 0.5),
    plot.subtitle = element_text(size = 9.5, hjust = 0.5),
    legend.position = "bottom", 
    panel.grid.minor = element_blank(),
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
    axis.ticks = element_line(color = "black", linewidth = 0.5),
    axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_pbg_suave)

# IPC Mensual

df_ipc_mensual <- read_excel(ruta_proxies, sheet = "IPC") %>%
  rename(fecha = 1, IPC = 2) %>%
  mutate(fecha = as.Date(fecha), IPC = as.numeric(IPC))

df_ipc_trimestral <- df_ipc_mensual %>%
  mutate(
    año = year(fecha),
    trim = quarter(fecha)
  ) %>%
  group_by(año, trim) %>%
  summarise(IPC_trim = mean(IPC, na.rm = TRUE), .groups = "drop")

# ==============================================================================
# 2. PROCESAMIENTO Y LIMPIEZA DE PROXIES COINCIDENTES
# ==============================================================================

# --- FUNCIÓN DE EXTRACCIÓN DE COMPONENTES (SEATS + HP) ---
# Esta función recibe el dataframe ya limpio, la columna a procesar y extrae:
# Serie Ajustada (SA), Tendencia-Ciclo (TC) y Tendencia Suavizada (HP).

extraer_componentes_ciclicos <- function(df, col_valor, freq_hp = lambda_hp_mensual) {
  ts_obj <- ts(df[[col_valor]], start = c(2010, 1), frequency = 12)
  
  fit <- suppressWarnings(seas(ts_obj))
  
  df$sa <- as.numeric(final(fit))
  df$tc <- as.numeric(trend(fit))
  
  hp_res <- hpfilter(ts(df$tc, start = c(2010, 1), frequency = 12), freq = freq_hp, type = "lambda")
  df$tc_suave_hp <- as.numeric(hp_res$trend)
  
  return(df)
}

# --- FUNCIÓN DE ANUALIZACIÓN Y CÁLCULO DE TVI ---

anualizar_y_calcular_tvi <- function(df, col_sa, metodo = "media") {
  df %>%
    group_by(año) %>%
    summarise(
      val_anual = if(metodo == "suma") sum(.data[[col_sa]], na.rm = TRUE) else mean(.data[[col_sa]], na.rm = TRUE), 
      .groups = "drop"
    ) %>%
    mutate(tvi_proxy = calc_tvi(val_anual)) # Usamos calc_tvi() creada en Bloque 0
}


# ------------------------------------------------------------------------------
# A. Remuneraciones Reales
# ------------------------------------------------------------------------------
df_remun_limpio <- read_excel(ruta_proxies, sheet = "Remuneración mensual") %>%
  rename(fecha = 1, remun_nom = 2) %>%
  mutate(
    fecha = as.Date(fecha), año = year(fecha),
    str_val = gsub(",", ".", gsub("\\.", "", as.character(remun_nom))),
    remun_nom = as.numeric(str_val)
  ) %>% filter(!is.na(remun_nom)) %>% arrange(fecha) %>%
  left_join(df_ipc_mensual, by = "fecha") %>%
  mutate(remun_real = (remun_nom / IPC) * 100)

df_remun_limpio <- extraer_componentes_ciclicos(df_remun_limpio, "remun_real") %>%
  rename(remun_sa = sa, remun_tc = tc)

df_remun_anual <- anualizar_y_calcular_tvi(df_remun_limpio, "remun_sa", metodo = "media")

# ------------------------------------------------------------------------------
# B. Empleo Registrado
# ------------------------------------------------------------------------------
df_empleo_limpio <- read_excel(ruta_proxies, sheet = "Empleo") %>%
  rename(fecha = 1, empleo_nom = 2) %>%
  mutate(fecha = as.Date(fecha), año = year(fecha), empleo = as.numeric(empleo_nom)) %>%
  filter(!is.na(empleo)) %>% arrange(fecha)

df_empleo_limpio <- extraer_componentes_ciclicos(df_empleo_limpio, "empleo") %>%
  rename(empleo_sa = sa, empleo_tc = tc)

df_empleo_anual <- anualizar_y_calcular_tvi(df_empleo_limpio, "empleo_sa", metodo = "media")

# ------------------------------------------------------------------------------
# C. Recursos Tributarios ATM
# ------------------------------------------------------------------------------
df_trib_limpio <- read_excel(ruta_proxies, sheet = "Tributarios mensual") %>%
  rename(fecha = 1, trib_nom = 2) %>%
  mutate(
    fecha = as.Date(fecha), año = year(fecha),
    str_val = gsub(",", "", gsub("[^0-9,.]", "", as.character(trib_nom))),
    trib_nom = as.numeric(str_val)
  ) %>% filter(!is.na(trib_nom)) %>% arrange(fecha) %>%
  left_join(df_ipc_mensual, by = "fecha") %>%
  mutate(trib_real = (trib_nom / IPC) * 100)

df_trib_limpio <- extraer_componentes_ciclicos(df_trib_limpio, "trib_real") %>%
  rename(trib_sa = sa, trib_tc = tc)

df_trib_anual <- anualizar_y_calcular_tvi(df_trib_limpio, "trib_sa", metodo = "suma")

# ------------------------------------------------------------------------------
# D. Ventas en Centros de Compra
# ------------------------------------------------------------------------------
df_centros_limpio <- read_excel(ruta_proxies, sheet = "Centros de compra") %>%
  rename(fecha = 1, centros_nom = 2) %>%
  mutate(fecha = as.Date(fecha), año = year(fecha), centros_nom = as.numeric(centros_nom)) %>%
  filter(!is.na(centros_nom)) %>% arrange(fecha) %>%
  left_join(df_ipc_mensual, by = "fecha") %>%
  mutate(centros_real = (centros_nom / IPC) * 100)

df_centros_limpio <- extraer_componentes_ciclicos(df_centros_limpio, "centros_real") %>%
  rename(centros_sa = sa, centros_tc = tc)

df_centros_anual <- anualizar_y_calcular_tvi(df_centros_limpio, "centros_sa", metodo = "suma")

# ------------------------------------------------------------------------------
# E y F. Series Descartadas (Gas y Supermercados)
# ------------------------------------------------------------------------------
df_gas_anual <- read_excel(ruta_proxies, sheet = "Gas") %>%
  rename(fecha = 1, gas = 2) %>%
  mutate(fecha = as.Date(fecha), año = year(fecha), gas = as.numeric(gas)) %>%
  group_by(año) %>% summarise(val_anual = sum(gas, na.rm = TRUE), .groups = "drop") %>%
  mutate(tvi_proxy = calc_tvi(val_anual))

df_super_anual <- read_excel(ruta_proxies, sheet = "Supermercados") %>%
  rename(fecha = 1, super_nom = 2) %>%
  mutate(
    fecha = as.Date(fecha), año = year(fecha),
    str_val = gsub(",", ".", gsub("\\.", "", as.character(super_nom))),
    super_nom = as.numeric(str_val)
  ) %>% left_join(df_ipc_mensual, by = "fecha") %>%
  mutate(super_real = (super_nom / IPC) * 100) %>%
  group_by(año) %>% summarise(val_anual = sum(super_real, na.rm = TRUE), .groups = "drop") %>%
  mutate(tvi_proxy = calc_tvi(val_anual))

# ------------------------------------------------------------------------------
# G. Hidrocarburos / Petróleo Procesado (m³)
# ------------------------------------------------------------------------------
df_petroleo_limpio <- read_excel(ruta_ica, sheet = "Hidrocarburos") %>%
  rename(fecha = 1, petroleo_nom = 2) %>%
  mutate(
    fecha = as.Date(fecha), 
    año = year(fecha),
    petroleo = as.numeric(petroleo_nom)
  ) %>% 
  filter(!is.na(petroleo) & fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% 
  arrange(fecha)

df_petroleo_limpio <- extraer_componentes_ciclicos(df_petroleo_limpio, "petroleo") %>%
  rename(petroleo_sa = sa, petroleo_tc = tc)

df_petroleo_anual <- anualizar_y_calcular_tvi(df_petroleo_limpio, "petroleo_sa", metodo = "suma")

# ------------------------------------------------------------------------------
# Consolidación del DataFrame Mensual (Proxies Coincidentes)
# ------------------------------------------------------------------------------
df_series_mensual <- list(
  df_remun_limpio %>% select(fecha, año, remun_sa, remun_tc),
  df_empleo_limpio %>% select(fecha, empleo_sa, empleo_tc),
  df_trib_limpio %>% select(fecha, trib_sa, trib_tc),
  df_centros_limpio %>% select(fecha, centros_sa, centros_tc),
  df_petroleo_limpio %>% select(fecha, petroleo_sa, petroleo_tc)
) %>%
  purrr::reduce(inner_join, by = "fecha") %>%
  arrange(fecha) %>%
  mutate(
    remun_sym    = calc_variacion_simetrica(remun_sa),
    empleo_sym   = calc_variacion_simetrica(empleo_sa),
    trib_sym     = calc_variacion_simetrica(trib_sa),
    centros_sym  = calc_variacion_simetrica(centros_sa),
    petroleo_sym = calc_variacion_simetrica(petroleo_sa)
  )

# ==============================================================================
# 3. TABLAS Y GRÁFICOS DE COMOVIMIENTO DE PROXIES VS. PBG
# ==============================================================================

# ------------------------------------------------------------------------------
# Métricas de Correlación Cruzada y Granger
# ------------------------------------------------------------------------------

obtener_metricas <- function(df_anual_proxy, nombre_proxy) {
  df_comp <- inner_join(df_pbg, df_anual_proxy, by = "año") %>% filter(!is.na(tvi_pbg) & !is.na(tvi_proxy))
  ccf_res <- ccf(df_comp$tvi_proxy, df_comp$tvi_pbg, lag.max = 2, plot = FALSE)
  r_k <- ccf_res$acf[,1,1]
  
  g1_fwd <- grangertest(tvi_pbg ~ tvi_proxy, order = 1, data = df_comp)
  g2_fwd <- grangertest(tvi_pbg ~ tvi_proxy, order = 2, data = df_comp)
  g1_rev <- grangertest(tvi_proxy ~ tvi_pbg, order = 1, data = df_comp)
  g2_rev <- grangertest(tvi_proxy ~ tvi_pbg, order = 2, data = df_comp)
  
  list(
    ccf = data.frame(
      Variable = nombre_proxy,
      Lag_m2 = round(r_k[1], 3), Lag_m1 = round(r_k[2], 3), Lag_0 = round(r_k[3], 3),
      Lag_p1 = round(r_k[4], 3), Lag_p2 = round(r_k[5], 3)
    ),
    granger = data.frame(
      Variable = nombre_proxy,
      F1_Lag1   = round(g1_fwd$F[2], 3), p1_Lag1 = round(g1_fwd$`Pr(>F)`[2], 4),
      F2_L1_Rev = round(g1_rev$F[2], 3), p2_L1_Rev = round(g1_rev$`Pr(>F)`[2], 4),
      F1_Lag2   = round(g2_fwd$F[2], 3), p1_Lag2 = round(g2_fwd$`Pr(>F)`[2], 4),
      F2_L2_Rev = round(g2_rev$F[2], 3), p2_L2_Rev = round(g2_rev$`Pr(>F)`[2], 4)
    )
  )
}

lista_proxies <- list(
  "Remuneración Real"      = df_remun_anual,
  "Empleo Registrado"      = df_empleo_anual,
  "Recaudación ATM Real"   = df_trib_anual,
  "Centros de Compra Real" = df_centros_anual,
  "Gas (Grandes Cons.)"    = df_gas_anual,
  "Ventas Supermercados"   = df_super_anual,
  "Petróleo Procesado (m³)" = df_petroleo_anual
)

res_ccf <- data.frame(); res_granger <- data.frame()
for (nom in names(lista_proxies)) {
  out <- obtener_metricas(lista_proxies[[nom]], nom)
  res_ccf <- bind_rows(res_ccf, out$ccf)
  res_granger <- bind_rows(res_granger, out$granger)
}

cat("\n==================================================================\n")
cat(" TABLA A.1: CORRELACIÓN CRUZADA DE PROXIES VS. PBG \n")
cat("==================================================================\n")
print(kable(res_ccf, col.names = c("Variable Proxy", "Lag -2", "Lag -1", "Lag 0 (Coincidente)", "Lag +1", "Lag +2")))

cat("\n==================================================================\n")
cat(" TABLA A.2: TEST DE CAUSALIDAD DE GRANGER (ESTADÍSTICOS F Y P-VALORES) \n")
cat("==================================================================\n")
print(kable(res_granger, col.names = c("Variable Proxy", "F1 (Proxy->PBG) L1", "p-val", "F2 (PBG->Proxy) L1", "p-val", "F1 (Proxy->PBG) L2", "p-val", "F2 (PBG->Proxy) L2", "p-val")))

# ------------------------------------------------------------------------------
# FUNCIONES DE GRÁFICOS DE COMOVIMIENTO PROXIES VS PBG 
# ------------------------------------------------------------------------------

graficar_comparacion_anual <- function(df_anual_proxy, titulo_proxy) {
  df_comp <- inner_join(df_pbg, df_anual_proxy, by = "año") %>% filter(!is.na(tvi_pbg) & !is.na(tvi_proxy))
  ggplot(df_comp, aes(x = año)) +
    geom_line(aes(y = tvi_pbg, color = "PBG Mendoza"), linewidth = 1.2) +
    geom_line(aes(y = tvi_proxy, color = titulo_proxy), linewidth = 1.2) +
    geom_hline(yintercept = 0, linetype = "dotted", color = "grey40") +
    scale_x_continuous(breaks = seq(2010, 2024, by = 2), limits = c(min(df_comp$año, na.rm = TRUE), max(df_comp$año, na.rm = TRUE)), expand = c(0, 0)) +
    coord_cartesian(clip = "off") +
    scale_color_manual(values = setNames(c(col_pbg, col_ics), c("PBG Mendoza", titulo_proxy))) +
    labs(
      title = NULL,
      subtitle = NULL,
      x = NULL, y = "TVI (%)", color = "Serie"
    ) +
    theme_minimal(base_size = 11, base_family = "Calibri") +
    theme(plot.title = element_text(face = "bold", hjust = 0.5), plot.subtitle = element_text(hjust = 0.5), legend.position = "bottom",
          panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
          axis.ticks = element_line(color = "black", linewidth = 0.5),
          axis.ticks.length = unit(0.15, "cm"),
          plot.margin = margin(t = 10, r = 15, b = 10, l = 15))
}

graficar_comparacion_hp <- function(df_mensual_proxy, col_suave_proxy, titulo_proxy) {
  df_proxy_hp_anual <- df_mensual_proxy %>%
    group_by(año) %>%
    summarise(val_hp = mean(.data[[col_suave_proxy]], na.rm = TRUE), .groups = "drop") %>%
    mutate(tvi_proxy_hp = calc_tvi(val_hp)) 
  
  df_pbg_hp <- df_pbg %>% mutate(tvi_pbg_hp = calc_tvi(pbg_suave_hp))
  df_comp_hp <- inner_join(df_pbg_hp, df_proxy_hp_anual, by = "año") %>% filter(!is.na(tvi_pbg_hp) & !is.na(tvi_proxy_hp))
  
  lbl_pbg <- "PBG Mendoza (HP)"; lbl_proxy <- paste(titulo_proxy, "(HP)")
  ggplot(df_comp_hp, aes(x = año)) +
    geom_line(aes(y = tvi_pbg_hp, color = lbl_pbg), linewidth = 1.2) +
    geom_line(aes(y = tvi_proxy_hp, color = lbl_proxy), linewidth = 1.2) +
    geom_hline(yintercept = 0, linetype = "dotted", color = "grey40") +
    scale_x_continuous(breaks = seq(2010, 2024, by = 2), limits = c(min(df_comp_hp$año, na.rm = TRUE), max(df_comp_hp$año, na.rm = TRUE)), expand = c(0, 0)) +
    coord_cartesian(clip = "off") +
    scale_color_manual(values = setNames(c(col_pbg, col_ics), c(lbl_pbg, lbl_proxy))) +
    labs(
      title = NULL,
      subtitle = NULL,
      x = NULL, y = "TVI (%)", color = "Serie"
    ) +
    theme_minimal(base_size = 11, base_family = "Calibri") +
    theme(plot.title = element_text(face = "bold", hjust = 0.5), plot.subtitle = element_text(hjust = 0.5), legend.position = "bottom",
          panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
          axis.ticks = element_line(color = "black", linewidth = 0.5),
          axis.ticks.length = unit(0.15, "cm"),
          plot.margin = margin(t = 10, r = 15, b = 10, l = 15))
}

# ------------------------------------------------------------------------------
# EJECUCIÓN E IMPRESIÓN MASIVA (Iteración limpia)
# ------------------------------------------------------------------------------

# 1. Impresión de Comovimientos Anuales
lista_proxies_graficos <- list(
  "Remuneración Real (s.e.)"      = df_remun_anual,
  "Empleo Registrado (s.e.)"      = df_empleo_anual,
  "Recaudación Real ATM (s.e.)"   = df_trib_anual,
  "Centros de Compra Real (s.e.)" = df_centros_anual,
  "Petróleo Procesado (s.e.)"     = df_petroleo_anual
)

purrr::iwalk(lista_proxies_graficos, ~ print(graficar_comparacion_anual(.x, .y)))

# 2. Impresión de Comovimientos HP y Puntos de Giro Bry-Boschan en Proxies Individuales
config_proxies_mensuales <- list(
  list(df = df_remun_limpio,    col_tc = "remun_tc",    tit_hp = "Remuneración Real",       tit_bb = "Remuneración Real",            ylab_bb = "Nivel Real",                  moneda = FALSE, entero = FALSE),
  list(df = df_empleo_limpio,   col_tc = "empleo_tc",   tit_hp = "Empleo Registrado",      tit_bb = "Empleo Registrado",            ylab_bb = "Puestos de trabajo",          moneda = FALSE, entero = TRUE),
  list(df = df_trib_limpio,     col_tc = "trib_tc",     tit_hp = "Recaudación Real ATM",   tit_bb = "Recaudación Real ATM",        ylab_bb = "Recaudación Real (Millones $)", moneda = TRUE,  entero = FALSE),
  list(df = df_centros_limpio,  col_tc = "centros_tc",  tit_hp = "Centros de Compra Real", tit_bb = "Ventas en Centros de Compra", ylab_bb = "Facturación Real (Millones $)", moneda = TRUE,  entero = FALSE),
  list(df = df_petroleo_limpio, col_tc = "petroleo_tc", tit_hp = "Petróleo Procesado",     tit_bb = "Petróleo Procesado (Hidrocarburos)", ylab_bb = "Volumen (m³)",         moneda = FALSE, entero = TRUE)
)

purrr::walk(config_proxies_mensuales, function(cfg) {
  print(graficar_comparacion_hp(cfg$df, "tc_suave_hp", cfg$tit_hp))
  
  pg_hp <- bry_boschan_nber(cfg$df, col_y = cfg$col_tc)
  
  plot_bb <- graficar_bry_boschan(
    df_plot = preparar_pg_plot(cfg$df, pg_hp), 
    col_tc_orig = cfg$col_tc, 
    col_tc_hp = "tc_suave_hp", 
    titulo_serie = cfg$tit_bb, 
    y_label = cfg$ylab_bb, 
    es_moneda = cfg$moneda, 
    es_entero = cfg$entero
  )
  print(plot_bb)
})

# ==============================================================================
# 4. CONSTRUCCIÓN Y EVALUACIÓN DEL ÍNDICE COINCIDENTE SINTÉTICO (ICS)
# Componentes (5): Remuneración Real, Empleo, ATM Real, Centros de Compra, Petróleo
# ==============================================================================

# ------------------------------------------------------------------------------
# 4.1 ESTIMACIÓN DE VOLATILIDADES Y PONDERADORES DE ESTANDARIZACIÓN (TCB)
# ------------------------------------------------------------------------------

df_volatilidad_ics <- df_series_mensual %>% 
  select(remun_sym, empleo_sym, trib_sym, centros_sym, petroleo_sym) %>% 
  drop_na()

std_devs_ics <- sapply(df_volatilidad_ics, sd)
inv_vol_ics  <- 1 / std_devs_ics
weights_ics  <- inv_vol_ics / sum(inv_vol_ics)

df_ponderadores_ics <- data.frame(
  Variable       = c("Remuneración Real", "Empleo Registrado", "Recaudación ATM Real", 
                     "Centros de Compra Real", "Petróleo Procesado (Hidrocarburos)"),
  Desviacion_Std = round(std_devs_ics, 4), 
  Inverso_Vol    = round(inv_vol_ics, 4),
  Ponderador     = round(weights_ics, 4), 
  Porcentaje     = paste0(round(weights_ics * 100, 2), "%")
)

cat("\n==================================================================\n")
cat(" TABLA DE PONDERADORES DEL ÍNDICE COINCIDENTE DE MENDOZA (5 COMPONENTES) \n")
cat("==================================================================\n")
print(kable(df_ponderadores_ics, col.names = c("Componente Coincidente", "Desv. Estándar (c_i)", "Amplitud Inversa (1/c_i)", "Ponderador (w_i)", "Peso Relativo (%)")))

# ------------------------------------------------------------------------------
# 4.2 PONDERACIÓN Y AGREGACIÓN MENSUAL DE VARIACIONES SIMÉTRICAS
# ------------------------------------------------------------------------------

df_series_mensual <- df_series_mensual %>%
  mutate(
    r_coincidente = ifelse(
      is.na(remun_sym), NA_real_,
      weights_ics["remun_sym"]    * remun_sym +
        weights_ics["empleo_sym"]   * empleo_sym +
        weights_ics["trib_sym"]     * trib_sym +
        weights_ics["centros_sym"]  * centros_sym +
        weights_ics["petroleo_sym"] * petroleo_sym
    )
  )

# ------------------------------------------------------------------------------
# 4.3 ENCADENAMIENTO VECTORIZADO Y RE-BASIFICACIÓN (BASE 2010 = 100)
# ------------------------------------------------------------------------------

idx_start_ics <- which(!is.na(df_series_mensual$r_coincidente))[1]
factores_crec <- (200 + df_series_mensual$r_coincidente) / (200 - df_series_mensual$r_coincidente)

factores_crec[idx_start_ics - 1] <- 100

factores_crec_calc <- ifelse(is.na(factores_crec), 1, factores_crec)
idx_ics <- cumprod(factores_crec_calc)

if (idx_start_ics > 2) {
  idx_ics[1:(idx_start_ics - 2)] <- NA
}

df_series_mensual$indice_coincidente_raw <- idx_ics
base_2010_ics <- mean(df_series_mensual$indice_coincidente_raw[df_series_mensual$año == 2010], na.rm = TRUE)

df_series_mensual <- df_series_mensual %>%
  mutate(
    indice_coincidente = (indice_coincidente_raw / base_2010_ics) * 100,
    ics_tc             = indice_coincidente
  )

# GRÁFICO: ICS Mensual (5 Componentes)
plot_indice_coincidente <- ggplot(df_series_mensual, aes(x = fecha, y = indice_coincidente)) +
  geom_line(color = col_ics, linewidth = 1.2) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_series_mensual$fecha, na.rm = TRUE), max(df_series_mensual$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "Índice (Base 2010 = 100)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(plot.title = element_text(face = "bold", size = 11, hjust = 0.5), plot.subtitle = element_text(size = 9.5, hjust = 0.5),
        panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
        axis.ticks = element_line(color = "black", linewidth = 0.5),
        axis.ticks.length = unit(0.15, "cm"),
        plot.margin = margin(t = 10, r = 15, b = 10, l = 15))
print(plot_indice_coincidente)

# ------------------------------------------------------------------------------
# 4.4 ANUALIZACIÓN DEL ICS Y VALIDACIÓN ECONOMÉTRICA VS. PBG
# ------------------------------------------------------------------------------

df_ics_anual <- df_series_mensual %>%
  filter(!is.na(indice_coincidente)) %>%
  group_by(año) %>%
  summarise(ics_anual = mean(indice_coincidente, na.rm = TRUE), n_meses = n(), .groups = "drop") %>%
  filter(n_meses == 12) %>% arrange(año) %>%
  mutate(tvi_ics = 100 * (ics_anual - lag(ics_anual)) / lag(ics_anual))

df_val_ics <- inner_join(df_pbg, df_ics_anual, by = "año") %>% filter(!is.na(tvi_pbg) & !is.na(tvi_ics))

# GRÁFICO 1: ICS Anualizado
plot_ics_anual <- ggplot(df_ics_anual, aes(x = año, y = ics_anual)) +
  geom_line(color = col_ics, linewidth = 1.2) +
  scale_x_continuous(breaks = seq(min(df_ics_anual$año), max(df_ics_anual$año), by = 2), limits = c(min(df_ics_anual$año, na.rm = TRUE), max(df_ics_anual$año, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  scale_y_continuous(labels = scales::comma) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "Índice (Base 2010 = 100)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(plot.title = element_text(face = "bold", size = 11, hjust = 0.5), plot.subtitle = element_text(size = 9.5, hjust = 0.5),
        panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
        axis.ticks = element_line(color = "black", linewidth = 0.5),
        axis.ticks.length = unit(0.15, "cm"),
        plot.margin = margin(t = 10, r = 15, b = 10, l = 15))
print(plot_ics_anual)

# ------------------------------------------------------------------------------
# EVALUACIÓN DE CORRELACIÓN Y CAUSALIDAD (CCF Y GRANGER)
# ------------------------------------------------------------------------------

# Correlograma Cruzado CCF: TVI ICS vs. TVI PBG
ccf_ics <- ccf(df_val_ics$tvi_ics, df_val_ics$tvi_pbg, lag.max = 2, plot = FALSE)
df_ccf_ics_resultados <- data.frame(
  Lag_Años = ccf_ics$lag[,1,1], Correlacion = round(ccf_ics$acf[,1,1], 4)
) %>% mutate(
  Significado = case_when(
    Lag_Años < 0  ~ "El Índice Coincidente Adelanta al PBG",
    Lag_Años == 0 ~ "Coincidencia Contemporánea",
    Lag_Años > 0  ~ "El Índice Coincidente está Rezagado respecto al PBG"
  )
)

cat("\n==================================================================\n")
cat(" CORRELACIÓN CRUZADA (CCF): TVI ÍNDICE COINCIDENTE vs. TVI PBG \n")
cat("==================================================================\n")
print(knitr::kable(df_ccf_ics_resultados, col.names = c("Lag (Años)", "Coef. Correlación (r)", "Interpretación Cíclica")))

# GRÁFICO 2: Correlograma Cruzado CCF
plot(ccf_ics, main = "Correlograma Cruzado: TVI ICS (5 Comp.) vs. TVI PBG", xlab = "Desfasaje en Años (Lag)", ylab = "Correlación Cruzada", ci.col = "red")

# Test de Granger ICS vs PBG
granger_ics_to_pbg_l1 <- lmtest::grangertest(tvi_pbg ~ tvi_ics, order = 1, data = df_val_ics)
granger_pbg_to_ics_l1 <- lmtest::grangertest(tvi_ics ~ tvi_pbg, order = 1, data = df_val_ics)

df_granger_ics <- data.frame(
  Direccion = c("ICS -> PBG (Proxy/Sintético predetermina al PBG)", "PBG -> ICS (PBG predetermina al ICS)"),
  Estadistico_F = c(round(granger_ics_to_pbg_l1$F[2], 4), round(granger_pbg_to_ics_l1$F[2], 4)), p_valor        = c(round(granger_ics_to_pbg_l1$`Pr(>F)`[2], 4), round(granger_pbg_to_ics_l1$`Pr(>F)`[2], 4))
)

cat("\n==================================================================\n")
cat(" TEST DE CAUSALIDAD DE GRANGER: TVI ÍNDICE COINCIDENTE VS. TVI PBG \n")
cat("==================================================================\n")
print(knitr::kable(df_granger_ics, col.names = c("Hipótesis Nula (Dirección)", "Estadístico F", "p-valor (Pr > F)")))

# GRÁFICO 3: Comovimiento Anual PBG vs. ICS
plot_val_ics_pbg <- ggplot(df_val_ics, aes(x = año)) +
  geom_line(aes(y = tvi_pbg, color = "PBG Mendoza"), linewidth = 1.2) +
  geom_line(aes(y = tvi_ics, color = "Índice Coincidente (ICS)"), linewidth = 1.2) +
  geom_hline(yintercept = 0, linetype = "dotted", color = "grey40") +
  scale_x_continuous(breaks = seq(min(df_val_ics$año), max(df_val_ics$año), by = 2), limits = c(min(df_val_ics$año, na.rm = TRUE), max(df_val_ics$año, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  scale_color_manual(name = "Serie", values = c("PBG Mendoza" = col_pbg, "Índice Coincidente (ICS)" = col_ics)) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "TVI (%)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(plot.title = element_text(face = "bold", hjust = 0.5), plot.subtitle = element_text(hjust = 0.5), legend.position = "bottom",
        panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
        axis.ticks = element_line(color = "black", linewidth = 0.5),
        axis.ticks.length = unit(0.15, "cm"),
        plot.margin = margin(t = 10, r = 15, b = 10, l = 15))
print(plot_val_ics_pbg)

# ------------------------------------------------------------------------------
# 4.5 SUAVIZADO SECUNDARIO HP Y CONCORDANCIA CÍCLICA
# ------------------------------------------------------------------------------

# PBG e ICS Suavizados HP Anual
ics_ts_a <- ts(df_ics_anual$ics_anual, start = min(df_ics_anual$año), frequency = 1)
hp_ics_a <- mFilter::hpfilter(ics_ts_a, freq = lambda_hp_anual, type = "lambda")

df_ics_hp_anual <- df_ics_anual %>% 
  mutate(
    ics_suave_hp = as.numeric(hp_ics_a$trend), 
    tvi_ics_hp = 100 * (ics_suave_hp - lag(ics_suave_hp)) / lag(ics_suave_hp)
  )

df_pbg_hp_anual <- df_pbg %>% 
  mutate(
    tvi_pbg_hp = 100 * (pbg_suave_hp - lag(pbg_suave_hp)) / lag(pbg_suave_hp)
  )

df_comp_hp_ics  <- inner_join(df_pbg_hp_anual, df_ics_hp_anual, by = "año") %>% 
  filter(!is.na(tvi_pbg_hp) & !is.na(tvi_ics_hp))

# GRÁFICO 4: Comovimiento Suavizado HP PBG vs ICS
plot_ics_hp_comparacion <- ggplot(df_comp_hp_ics, aes(x = año)) +
  geom_line(aes(y = tvi_pbg_hp, color = "PBG (suavizado HP)"), linewidth = 1.2) +
  geom_line(aes(y = tvi_ics_hp, color = "ICS (suavizado HP)"), linewidth = 1.2) +
  geom_hline(yintercept = 0, linetype = "dotted", color = "grey40") +
  scale_x_continuous(breaks = seq(min(df_comp_hp_ics$año), max(df_comp_hp_ics$año), by = 2), limits = c(min(df_comp_hp_ics$año, na.rm = TRUE), max(df_comp_hp_ics$año, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  scale_color_manual(name = "Serie", values = c("PBG (suavizado HP)" = col_pbg, "ICS (suavizado HP)" = col_ics)) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "TVI (%)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(plot.title = element_text(face = "bold", hjust = 0.5), plot.subtitle = element_text(hjust = 0.5), legend.position = "bottom",
        panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
        axis.ticks = element_line(color = "black", linewidth = 0.5),
        axis.ticks.length = unit(0.15, "cm"),
        plot.margin = margin(t = 10, r = 15, b = 10, l = 15))

print(plot_ics_hp_comparacion)

# Concordancia Cíclica Harding & Pagan
df_val_concordancia <- df_val_ics %>% 
  mutate(
    S_pbg = ifelse(tvi_pbg > 0, 1, 0), 
    S_ics = ifelse(tvi_ics > 0, 1, 0), 
    Coincide_Fase = ifelse(S_pbg == S_ics, 1, 0)
  )
ci_harding_pagan <- mean(df_val_concordancia$Coincide_Fase)

cat("\n==================================================================\n")
cat(" ÍNDICE DE CONCORDANCIA DE HARDING & PAGAN (ICS vs. PBG) \n")
cat("==================================================================\n")
cat("Porcentaje de fases cíclicas coincidentes (CI):", round(ci_harding_pagan * 100, 2), "%\n")

# ------------------------------------------------------------------------------
# 4.6 PUNTOS DE GIRO BRY-BOSCHAN SOBRE ICS MENSUAL
# ------------------------------------------------------------------------------

# Suavizado HP Mensual
ics_ts_m <- ts(df_series_mensual$indice_coincidente[!is.na(df_series_mensual$indice_coincidente)], start = c(2010, 1), frequency = 12)
hp_ics_m <- mFilter::hpfilter(ics_ts_m, freq = lambda_hp_mensual, type = "lambda")
df_series_mensual$ics_suave_hp <- ifelse(is.na(df_series_mensual$indice_coincidente), NA_real_, as.numeric(hp_ics_m$trend))

pg_ics_hp <- bry_boschan_nber(df_series_mensual %>% filter(!is.na(ics_tc)), col_y = "ics_tc")

# GRÁFICO 5: Puntos de Giro Bry-Boschan en ICS
plot_bb_ics_hp <- graficar_bry_boschan(
  df_plot = preparar_pg_plot(as.data.frame(df_series_mensual), pg_ics_hp),
  col_tc_orig = "ics_tc", 
  col_tc_hp = "ics_suave_hp", 
  titulo_serie = "Índice Coincidente Sintético (ICS-Mza)", 
  y_label = "Índice (Base 2010 = 100)", 
  color_serie = col_ics
)
print(plot_bb_ics_hp)

# Auditoría de Tiempos
audit_ics_hp <- auditar_tiempos_bb(pg_ics_hp, df_serie = as.data.frame(df_series_mensual))
cat("\n==================================================================\n")
cat(" AUDITORÍA DE FASES Y CICLOS BRY-BOSCHAN (ICS) \n")
cat("==================================================================\n")
print(knitr::kable(audit_ics_hp, align = "c"))

# ------------------------------------------------------------------------------
# 4.7 EVALUACIÓN DE PRECISIÓN CUANTITATIVA Y ERROR DE TRACKING 
# ------------------------------------------------------------------------------

df_errores_observados <- df_val_ics %>%
  filter(!is.na(tvi_pbg) & !is.na(tvi_ics)) %>%
  mutate(
    error_abs = abs(tvi_pbg - tvi_ics),
    error_sq  = (tvi_pbg - tvi_ics)^2
  )

mae_obs  <- mean(df_errores_observados$error_abs)
rmse_obs <- sqrt(mean(df_errores_observados$error_sq))

df_errores_hp <- df_comp_hp_ics %>%
  filter(!is.na(tvi_pbg_hp) & !is.na(tvi_ics_hp)) %>%
  mutate(
    error_abs_hp = abs(tvi_pbg_hp - tvi_ics_hp),
    error_sq_hp  = (tvi_pbg_hp - tvi_ics_hp)^2
  )

mae_hp  <- mean(df_errores_hp$error_abs_hp)
rmse_hp <- sqrt(mean(df_errores_hp$error_sq_hp))

df_resumen_errores <- data.frame(
  Tratamiento = c("Series observadas (brutas)", "Series suavizadas (filtro HP)"),
  `MAE (p.p.)`  = c(sprintf("%.2f", mae_obs), sprintf("%.2f", mae_hp)),
  `RMSE (p.p.)` = c(sprintf("%.2f", rmse_obs), sprintf("%.2f", rmse_hp)),
  check.names = FALSE
)

cat("\n==================================================================\n")
cat(" EVALUACIÓN DE PRECISIÓN CUANTITATIVA Y ERROR DE TRACKING \n")
cat("==================================================================\n")
print(knitr::kable(df_resumen_errores, align = c("l", "c", "c")))

df_detalle_anual_error <- df_errores_observados %>%
  transmute(
    Año = año,
    `TVI PBG (%)` = round(tvi_pbg, 2),
    `TVI ICS-Mza (%)` = round(tvi_ics, 2),
    `Error Absoluto (p.p.)` = round(error_abs, 2)
  )

cat("\n==================================================================\n")
cat(" DETALLE ANUAL DE ERRORES DE SEGUIMIENTO (OBSERVADOS) \n")
cat("==================================================================\n")
print(knitr::kable(df_detalle_anual_error, align = "c"))

# ==============================================================================
# 5. PROCESAMIENTO Y ESTIMACIÓN DE VARIABLES ADELANTADAS
# ==============================================================================

# ------------------------------------------------------------------------------
# FUNCIÓN GENÉRICA PARA EXTRACCIÓN DE TENDENCIA (TC) Y SUAVIZADO (HP)
# ------------------------------------------------------------------------------
procesar_tendencias_mensuales <- function(df, col_valor, freq_hp = lambda_hp_mensual, log_transform = FALSE) {
  col_fecha <- if("fecha" %in% names(df)) "fecha" else "Fecha"
  
  anio_inicio <- lubridate::year(min(df[[col_fecha]]))
  mes_inicio  <- lubridate::month(min(df[[col_fecha]]))
  
  ts_obj <- ts(df[[col_valor]], start = c(anio_inicio, mes_inicio), frequency = 12)
  
  fit_x13 <- suppressWarnings(seas(ts_obj))
  ts_tc   <- trend(fit_x13)
  ts_sa   <- final(fit_x13)
  
  serie_hp <- if(log_transform) log(ts_sa) else ts_tc
  hp_res   <- hpfilter(serie_hp, freq = freq_hp, type = "lambda")
  
  df$tc_obj_ts <- as.numeric(ts_tc)
  df$sa_obj_ts <- as.numeric(ts_sa)
  
  if(log_transform) {
    df$tc_suave_hp <- as.numeric(hp_res$cycle)
  } else {
    df$tc_suave_hp <- as.numeric(hp_res$trend)
  }
  
  return(df)
}

# ------------------------------------------------------------------------------
# 1. Despachos de Cemento
# ------------------------------------------------------------------------------
df_cemento_nacional <- read_excel(ruta_ica, sheet = "Cemento Nacional")
cemento_nac_ts <- ts(df_cemento_nacional$`Despacho interno`, start = c(2010, 1), frequency = 12)
cemento_nac_ts[time(cemento_nac_ts) == 2017 + (1/12)] <- NA
cemento_nac_guia <- ts(as.numeric(na.interp(cemento_nac_ts)), start = c(2010, 1), frequency = 12)

df_c1_largo <- read_excel(ruta_ica, sheet = "Cemento 1") %>%
  pivot_longer(cols = contains("Trimestre"), names_to = "trimestre", values_to = "cemento") %>% arrange(Año)

cemento1_trim_ts <- ts(df_c1_largo$cemento, start = c(2010, 1), frequency = 4)
modelo_cemento   <- td(cemento1_trim_ts ~ cemento_nac_guia, method = "fast")
cemento1_mensual_ts <- predict(modelo_cemento)

df_c1_limpio <- ts_df(cemento1_mensual_ts) %>% rename(fecha = time, cemento = value) %>% mutate(fecha = as.Date(fecha))

df_c2_limpio <- read_excel(ruta_ica, sheet = "Cemento 2") %>%
  rename(anio = 1, mes_nombre = 2, cemento = 3) %>%
  mutate(
    mes_nombre = tolower(trimws(mes_nombre)), mes_num = meses_num[mes_nombre],
    anio = as.numeric(anio), cemento = as.numeric(gsub("\\.", "", cemento)),
    fecha = ym(paste(anio, mes_num, sep = "-"))
  ) %>% arrange(fecha) %>% select(fecha, cemento)

df_cemento_completo <- bind_rows(df_c1_limpio %>% filter(fecha < min(df_c2_limpio$fecha)), df_c2_limpio) %>% arrange(fecha)

df_cemento_completo <- procesar_tendencias_mensuales(df_cemento_completo, "cemento") %>% rename(cemento_tc = tc_obj_ts)

# ------------------------------------------------------------------------------
# 2. ITCRM Mendoza
# ------------------------------------------------------------------------------
df_itcrm_limpio <- read_excel(ruta_ica, sheet = "ITCRM", range = cell_cols(1:2), col_types = c("date", "numeric")) %>%
  rename(fecha = 1, itcrm = 2) %>%
  mutate(fecha = floor_date(as.Date(fecha), "month")) %>%
  group_by(fecha) %>% summarise(itcrm = mean(itcrm, na.rm = TRUE), .groups = "drop") %>%
  filter(fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% arrange(fecha)

df_itcrm_limpio <- procesar_tendencias_mensuales(df_itcrm_limpio, "itcrm") %>% rename(itcrm_tc = tc_obj_ts)

# ------------------------------------------------------------------------------
# 3. Comercio Automotor
# ------------------------------------------------------------------------------
df_auto_limpio <- read_excel(ruta_ica, sheet = "Automotor", range = cell_cols(1:2)) %>%
  rename(fecha_raw = 1, auto = 2) %>%
  mutate(
    mes_str  = substr(tolower(gsub("[^a-z]", "", fecha_raw)), 1, 3), 
    mes_num  = meses_num[mes_str],
    anio_raw = as.numeric(gsub("[^0-9]", "", fecha_raw)),
    anio_num = ifelse(anio_raw < 100, 2000 + anio_raw, anio_raw),
    fecha    = ym(paste(anio_num, mes_num, sep = "-")), 
    auto     = as.numeric(gsub("\\.", "", auto))
  ) %>% 
  filter(fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% 
  arrange(fecha) %>% 
  select(fecha, auto)

df_auto_limpio <- procesar_tendencias_mensuales(df_auto_limpio, "auto") %>% rename(auto_tc = tc_obj_ts)

pg_auto_tc <- bry_boschan_nber(df_auto_limpio, col_y = "auto_tc")

print(
  graficar_bry_boschan(
    df_plot      = preparar_pg_plot(df_auto_limpio, pg_auto_tc),
    col_tc_orig  = "auto_tc",
    col_tc_hp    = "tc_suave_hp", # ← Crucial para que aparezca la línea suavizada
    titulo_serie = "Comercio Automotor",
    y_label      = "Unidades",
    es_entero    = TRUE, 
    color_serie  = col_ica
  )
)

# ------------------------------------------------------------------------------
# 4. Ratio Préstamos / Depósitos
# ------------------------------------------------------------------------------
df_pd_nac_limpio <- read_excel(ruta_ica, sheet = "Préstamos - depósitos N") %>%
  rename(fecha = 1, prestamos_nac = 2, depositos_nac = 3) %>%
  mutate(
    fecha = as.Date(fecha),
    prestamos_nac = as.numeric(gsub("\\.", "", prestamos_nac)), depositos_nac = as.numeric(gsub("\\.", "", depositos_nac)),
    ratio_nac = prestamos_nac / depositos_nac
  ) %>% filter(fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% arrange(fecha)

ratio_nac_mens_ts <- ts(df_pd_nac_limpio$ratio_nac, start = c(2010, 1), frequency = 12)

df_pd_prov_trim <- read_excel(ruta_ica, sheet = "Préstamos - depósitos") %>%
  rename(periodo = 1, prestamos_prov = 2, depositos_prov = 3) %>%
  separate(periodo, into = c("trim", "anio"), sep = "-") %>%
  mutate(
    trim = as.numeric(gsub("[^0-9]", "", trim)), anio = as.numeric(anio),
    prestamos_prov = as.numeric(gsub("\\.", "", prestamos_prov)), depositos_prov = as.numeric(gsub("\\.", "", depositos_prov)),
    ratio_prov = prestamos_prov / depositos_prov
  ) %>% arrange(anio, trim)

ratio_prov_trim_ts  <- ts(df_pd_prov_trim$ratio_prov, start = c(2010, 1), frequency = 4)
modelo_pd           <- td(ratio_prov_trim_ts ~ ratio_nac_mens_ts, method = "fast")
ratio_prov_mens_ts  <- predict(modelo_pd)

df_pd_mensual <- data.frame(fecha = df_pd_nac_limpio$fecha, ratio_prov = as.numeric(ratio_prov_mens_ts))

df_pd_mensual <- procesar_tendencias_mensuales(df_pd_mensual, "ratio_prov") %>% rename(ratio_tc = tc_obj_ts)

# ------------------------------------------------------------------------------
# 5. Motovehículos
# ------------------------------------------------------------------------------
df_moto_limpio <- read_excel(ruta_ica, sheet = "Motovehículo", range = cell_cols(1:2)) %>%
  rename(fecha_raw = 1, moto = 2) %>%
  mutate(fecha = df_auto_limpio$fecha, moto = as.numeric(gsub("\\.", "", moto))) %>%
  filter(fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% arrange(fecha) %>% select(fecha, moto)

df_moto_limpio <- procesar_tendencias_mensuales(df_moto_limpio, "moto") %>% rename(moto_tc = tc_obj_ts)

pg_moto_tc <- bry_boschan_nber(df_moto_limpio %>% filter(!is.na(moto_tc)), col_y = "moto_tc")

print(
  graficar_bry_boschan(
    df_plot      = preparar_pg_plot(df_moto_limpio, pg_moto_tc),
    col_tc_orig  = "moto_tc",
    col_tc_hp    = "tc_suave_hp",
    titulo_serie = "Motovehículos",
    y_label      = "Unidades",
    es_entero    = TRUE, 
    color_serie  = col_ica
  )
)

# ------------------------------------------------------------------------------
# 6. Escrituras de Compraventa
# ------------------------------------------------------------------------------
df_escrituras_limpio <- read_excel(ruta_ica, sheet = "Escrituras") %>%
  rename(mes_nombre = 1) %>%
  filter(!tolower(trimws(mes_nombre)) %in% c("total", "total ")) %>%
  mutate(across(-mes_nombre, as.character)) %>%
  pivot_longer(cols = -mes_nombre, names_to = "anio", values_to = "escrituras_raw") %>%
  mutate(
    escrituras_str = gsub("\\.", "", escrituras_raw),
    escrituras_str = ifelse(trimws(escrituras_str) %in% c("-", "", "NA"), NA, escrituras_str),
    escrituras     = as.numeric(escrituras_str),
    mes_num        = meses_num[tolower(trimws(mes_nombre))],
    anio_num       = as.numeric(anio),
    fecha          = ym(paste(anio_num, mes_num, sep = "-"))
  ) %>% filter(fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% arrange(fecha) %>% select(fecha, escrituras) %>%
  mutate(escrituras_estimada = zoo::na.approx(escrituras, na.rm = FALSE))

df_escrituras_limpio <- procesar_tendencias_mensuales(df_escrituras_limpio, "escrituras_estimada") %>% rename(escrituras_tc = tc_obj_ts)

pg_escrituras_tc <- bry_boschan_nber(df_escrituras_limpio %>% filter(!is.na(escrituras_tc)), col_y = "escrituras_tc")

print(
  graficar_bry_boschan(
    df_plot      = preparar_pg_plot(df_escrituras_limpio, pg_escrituras_tc),
    col_tc_orig  = "escrituras_tc",
    col_tc_hp    = "tc_suave_hp",
    titulo_serie = "Escrituras de Compraventa",
    y_label      = "Escrituras",
    es_entero    = TRUE, 
    color_serie  = col_ica
  )
)

# ------------------------------------------------------------------------------
# 7. Destilado de Hidrocarburos (Petróleo procesado en m³)
# ------------------------------------------------------------------------------
df_petroleo_limpio <- read_excel(ruta_ica, sheet = "Hidrocarburos") %>%
  rename(fecha = 1, petroleo = 2) %>%
  mutate(fecha = as.Date(fecha), petroleo = as.numeric(petroleo)) %>%
  filter(fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% arrange(fecha)

df_petroleo_limpio <- procesar_tendencias_mensuales(df_petroleo_limpio, "petroleo") %>% rename(petroleo_tc = tc_obj_ts)

# ------------------------------------------------------------------------------
# 8. Ocupación hotelera (promedio GM %)
# ------------------------------------------------------------------------------
df_hotel_limpio <- read_excel(ruta_ica, sheet = "Hotel") %>%
  rename(fecha = 1, hotel_raw = 2) %>%
  mutate(
    fecha = as.Date(fecha),
    hotel_str = gsub("%", "", as.character(hotel_raw)),
    hotel_str = gsub(",", ".", hotel_str),
    hotel_num = as.numeric(trimws(hotel_str)),
    hotel_num = ifelse(hotel_num == 0, NA_real_, hotel_num),
    hotel_clean = zoo::na.approx(hotel_num, na.rm = FALSE)
  ) %>% filter(fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% arrange(fecha)

df_hotel_limpio <- procesar_tendencias_mensuales(df_hotel_limpio, "hotel_clean") %>% rename(hotel_tc = tc_obj_ts)

# ------------------------------------------------------------------------------
# 9. Préstamos al sec. privado no financiero.
# ------------------------------------------------------------------------------
df_prestamos_mza_raw <- read_excel(ruta_ica, sheet = "Préstamos") %>%
  rename(fecha_str = 1, prestamos_nom = 2) %>%
  filter(!is.na(prestamos_nom)) %>%
  mutate(
    año  = as.numeric(sub(".*-", "", fecha_str)),
    trim = as.numeric(sub("T-.*", "", fecha_str)),
    str_val = gsub(",", ".", gsub("\\.", "", as.character(prestamos_nom))),
    prestamos_nom = as.numeric(str_val)
  ) %>%
  left_join(df_ipc_trimestral, by = c("año", "trim")) %>%
  mutate(prestamos_real = (prestamos_nom / IPC_trim) * 100) %>% arrange(año, trim)

df_prestamos_nac_raw <- read_excel(ruta_ica, sheet = "Préstamos N") %>%
  rename(fecha = 1, prestamos_nac_nom = 2) %>%
  filter(!is.na(prestamos_nac_nom)) %>%
  mutate(
    fecha = as.Date(fecha),
    str_val = gsub(",", ".", gsub("\\.", "", as.character(prestamos_nac_nom))),
    prestamos_nac_nom = as.numeric(str_val)
  ) %>%
  left_join(df_ipc_mensual, by = "fecha") %>%
  mutate(prestamos_nac_real = (prestamos_nac_nom / IPC) * 100) %>%
  filter(fecha >= as.Date("2010-01-01") & fecha <= as.Date("2024-12-01")) %>% arrange(fecha)

prestamos_mza_trim_ts <- ts(df_prestamos_mza_raw$prestamos_real, start = c(2010, 1), frequency = 4)
prestamos_nac_guia_ts <- ts(df_prestamos_nac_raw$prestamos_nac_real, start = c(2010, 1), frequency = 12)

mod_prestamos <- td(prestamos_mza_trim_ts ~ prestamos_nac_guia_ts, method = "fast")
prestamos_mza_mensual_ts <- predict(mod_prestamos)

df_prestamos_limpio <- data.frame(
  fecha = seq(from = as.Date("2010-01-01"), to = as.Date("2024-12-01"), by = "month"),
  prestamos_real = as.numeric(prestamos_mza_mensual_ts)
) %>% mutate(año = year(fecha))

df_prestamos_limpio <- procesar_tendencias_mensuales(df_prestamos_limpio, "prestamos_real") %>% rename(prestamos_tc = tc_obj_ts, prestamos_sa = sa_obj_ts)

df_prestamos_anual <- df_prestamos_limpio %>%
  group_by(año) %>%
  summarise(val_anual = mean(prestamos_tc, na.rm = TRUE), .groups = "drop") %>%
  mutate(tvi_proxy = 100 * (val_anual - lag(val_anual)) / lag(val_anual))

# ------------------------------------------------------------------------------
# 10. VENTA DE COMBUSTIBLES (PROCESAMIENTO TC)
# ------------------------------------------------------------------------------
df_combustibles_raw <- read_excel("02 - ICA base de datos.xlsx", sheet = "Combustible")

df_combustibles <- df_combustibles_raw %>%
  dplyr::select(fecha = 1, Gasoil_total, Nafta_premium, Naftas_totales) %>%
  dplyr::mutate(
    fecha          = as.Date(fecha),
    Gasoil_total   = as.numeric(Gasoil_total),
    Nafta_premium  = as.numeric(Nafta_premium),
    Naftas_totales = as.numeric(Naftas_totales)
  )

procesar_serie_tc <- function(df, col_valor, freq_hp = 14400) {
  col_fecha <- if("fecha" %in% names(df)) "fecha" else "Fecha"
  df_temp <- df %>% select(all_of(col_fecha), all_of(col_valor)) %>% filter(!is.na(.data[[col_fecha]]))
  
  serie_vec <- df_temp[[col_valor]]
  serie_clean <- ifelse(serie_vec <= 0, NA, serie_vec)
  df_temp[[col_valor]] <- zoo::na.locf(zoo::na.approx(serie_clean, na.rm = FALSE), na.rm = FALSE)
  
  df_procesado <- procesar_tendencias_mensuales(df_temp, col_valor, freq_hp = freq_hp, log_transform = TRUE)
  return(df_procesado)
}

res_gasoil     <- procesar_serie_tc(df_combustibles, "Gasoil_total")
res_nafta_prem <- procesar_serie_tc(df_combustibles, "Nafta_premium")
res_naftas_tot <- procesar_serie_tc(df_combustibles, "Naftas_totales")

df_ciclos_combustibles <- tibble::tibble(
  fecha         = df_combustibles$fecha,
  gasoil_tc     = res_gasoil$tc_obj_ts,     # Extracción de la TC cruda
  nafta_prem_tc = res_nafta_prem$tc_obj_ts, # Extracción de la TC cruda
  nafta_tot_tc  = res_naftas_tot$tc_obj_ts  # Extracción de la TC cruda
)

# ------------------------------------------------------------------------------
# 11. DESPACHO DE VINO APTO PARA EL CONSUMO
# ------------------------------------------------------------------------------
df_vino_raw <- read_excel("02 - ICA base de datos.xlsx", sheet = "Vino")

df_vino <- df_vino_raw %>%
  dplyr::select(fecha = fecha, Despachos = Despachos) %>%
  dplyr::mutate(fecha = as.Date(fecha), Despachos = as.numeric(Despachos))

df_vino_limpio <- procesar_serie_tc(df_vino, "Despachos") %>% 
  rename(vino_tc = tc_obj_ts) %>%
  select(fecha, vino_tc)

# ------------------------------------------------------------------------------
# 12. EXPORTACIONES (Denton-Cholette Trimestral a Mensual + TC)
# ------------------------------------------------------------------------------
df_exp_raw <- read_excel("02 - ICA base de datos.xlsx", sheet = "Exportación")

df_exp <- df_exp_raw %>%
  dplyr::select(
    Trimestre      = 1, Total_General  = 2, MOA_Total      = 3, MOA_Bebidas    = 4,
    MOI_Total      = 5, Prod_Primarios = 6, Comb_Energia   = 7
  ) %>%
  dplyr::mutate(across(-Trimestre, ~ as.numeric(gsub(",", ".", as.character(.)))))

procesar_exportacion_trimestral <- function(serie_vec, inicio_anio = 2012, inicio_trim = 1, lambda = 14400) {
  ts_q <- ts(serie_vec, start = c(inicio_anio, inicio_trim), frequency = 4)
  td_model <- tempdisagg::td(ts_q ~ 1, conversion = "sum", method = "denton-cholette")
  ts_m <- predict(td_model)
  
  num_meses    <- length(ts_m)
  fecha_inicio <- as.Date(paste0(inicio_anio, "-01-01"))
  fechas_m     <- seq.Date(from = fecha_inicio, by = "month", length.out = num_meses)
  
  df_temp <- data.frame(fecha = fechas_m, exp_val = as.numeric(ts_m))
  df_proc <- procesar_tendencias_mensuales(df_temp, "exp_val", freq_hp = lambda, log_transform = TRUE)
  
  return(tibble::tibble(
    fecha       = fechas_m,
    ts_m        = as.numeric(ts_m),
    ts_sa       = df_proc$sa_obj_ts,
    tc_pura     = df_proc$tc_obj_ts # Extraemos la TC
  ))
}

df_var_exp_tot  <- procesar_exportacion_trimestral(df_exp$Total_General) %>% dplyr::select(fecha, exp_total_tc = tc_pura)
df_var_exp_moat <- procesar_exportacion_trimestral(df_exp$MOA_Total) %>% dplyr::select(fecha, exp_moat_tc  = tc_pura)
df_var_exp_moab <- procesar_exportacion_trimestral(df_exp$MOA_Bebidas) %>% dplyr::select(fecha, exp_moab_tc  = tc_pura)
df_var_exp_moit <- procesar_exportacion_trimestral(df_exp$MOI_Total) %>% dplyr::select(fecha, exp_moit_tc  = tc_pura)
df_var_exp_prim <- procesar_exportacion_trimestral(df_exp$Prod_Primarios) %>% dplyr::select(fecha, exp_prim_tc  = tc_pura)
df_var_exp_comb <- procesar_exportacion_trimestral(df_exp$Comb_Energia) %>% dplyr::select(fecha, exp_comb_tc  = tc_pura)

df_exportaciones_consolidado <- list(df_var_exp_tot, df_var_exp_moat, df_var_exp_moab, df_var_exp_moit, df_var_exp_prim, df_var_exp_comb) %>% 
  purrr::reduce(dplyr::full_join, by = "fecha") %>% dplyr::arrange(fecha)

# ------------------------------------------------------------------------------
# 13. VARIABLES MONETARIAS NACIONALES: M2 y Caja de Ahorro
# ------------------------------------------------------------------------------
df_m2_raw <- read_excel(ruta_ica, sheet = "M2")

df_m2_limpio <- df_m2_raw %>%
  rename(fecha = 1, m2_nominal = M2_Moneda_Nacional_Millones, caja_ahorro_nominal = Caja_Ahorro_MN_Total_Millones) %>%
  mutate(fecha = as.Date(fecha), m2_nominal = as.numeric(m2_nominal), caja_ahorro_nominal = as.numeric(caja_ahorro_nominal)) %>%
  filter(!is.na(fecha)) %>% arrange(fecha)

df_m2_real <- df_m2_limpio %>%
  inner_join(df_ipc_mensual, by = "fecha") %>%
  mutate(m2_real = (m2_nominal / IPC) * 100, caja_ahorro_real = (caja_ahorro_nominal / IPC) * 100)

df_m2_procesado          <- procesar_serie_tc(df_m2_real, "m2_real", freq_hp = lambda_hp_mensual)
df_caja_ahorro_procesado <- procesar_serie_tc(df_m2_real, "caja_ahorro_real", freq_hp = lambda_hp_mensual)

df_var_m2          <- df_m2_procesado %>% select(fecha, m2_tc = tc_obj_ts)
df_var_caja_ahorro <- df_caja_ahorro_procesado %>% select(fecha, caja_ahorro_tc = tc_obj_ts)

# ------------------------------------------------------------------------------
# 14. VARIABLES MONETARIAS NACIONALES: M0 (Base Monetaria y Circulación)
# ------------------------------------------------------------------------------
df_m0_raw <- read_excel(ruta_ica, sheet = "M0")

df_m0_limpio <- df_m0_raw %>%
  rename(fecha = 1, base_mon_nominal = Base_Monetaria_Total_Millones, circulacion_nominal = Circulacion_Publico_Millones) %>%
  mutate(fecha = as.Date(fecha), base_mon_nominal = as.numeric(base_mon_nominal), circulacion_nominal = as.numeric(circulacion_nominal)) %>%
  filter(!is.na(fecha)) %>% arrange(fecha)

df_m0_real <- df_m0_limpio %>%
  inner_join(df_ipc_mensual, by = "fecha") %>%
  mutate(base_mon_real = (base_mon_nominal / IPC) * 100, circulacion_real = (circulacion_nominal / IPC) * 100)

df_base_mon_procesado    <- procesar_serie_tc(df_m0_real, "base_mon_real", freq_hp = lambda_hp_mensual)
df_circulacion_procesado <- procesar_serie_tc(df_m0_real, "circulacion_real", freq_hp = lambda_hp_mensual)

df_var_base_mon    <- df_base_mon_procesado %>% select(fecha, base_mon_tc = tc_obj_ts)
df_var_circulacion <- df_circulacion_procesado %>% select(fecha, circulacion_tc = tc_obj_ts)

# ==============================================================================
# EVALUACIÓN DE VARIABLES ADELANTADAS VS. ÍNDICE COINCIDENTE SINTÉTICO (ICS)
# Test de Correlación Cruzada (CCF) y Test de Causalidad de Granger
# Transformación Estacionaria: Tasas de Variación Simétrica sobre series TC Puras
# ==============================================================================

calc_variacion_simetrica <- function(x) {
  200 * (x - dplyr::lag(x, 1)) / (x + dplyr::lag(x, 1))
}

# ------------------------------------------------------------------------------
# A. EXTRACCIÓN Y TRANSFORMACIÓN ESTACIONARIA DE LA SERIE TARGET (ICS)
# ------------------------------------------------------------------------------

df_ics_norm <- df_series_mensual
colnames(df_ics_norm) <- tolower(colnames(df_ics_norm))

if ("fecha" %in% names(df_ics_norm)) {
  df_ics_norm <- df_ics_norm[, !duplicated(names(df_ics_norm))]
}

df_ics_target <- df_ics_norm %>%
  dplyr::select(fecha, ics_tc) %>%
  dplyr::arrange(fecha) %>%
  dplyr::mutate(ics_target = calc_variacion_simetrica(ics_tc)) %>%
  dplyr::filter(!is.na(fecha), !is.na(ics_target)) %>%
  dplyr::select(fecha, ics_target)

# ------------------------------------------------------------------------------
# B. CONSOLIDACIÓN DE VARIABLES ADELANTADAS (23 VARIABLES EN TC)
# ------------------------------------------------------------------------------

lista_df_adelantadas <- list(
  df_cemento_completo    %>% dplyr::select(fecha, cemento_var      = cemento_tc),
  df_itcrm_limpio        %>% dplyr::select(fecha, itcrm_var        = itcrm_tc),
  df_auto_limpio         %>% dplyr::select(fecha, auto_var         = auto_tc),
  df_pd_mensual          %>% dplyr::select(fecha, ratio_var        = ratio_tc),
  df_moto_limpio         %>% dplyr::select(fecha, moto_var         = moto_tc),
  df_escrituras_limpio   %>% dplyr::select(fecha, escrituras_var  = escrituras_tc),
  df_petroleo_limpio     %>% dplyr::select(fecha, petroleo_var    = petroleo_tc),
  df_hotel_limpio        %>% dplyr::select(fecha, hotel_var        = hotel_tc),
  df_prestamos_limpio    %>% dplyr::select(fecha, prestamos_var   = prestamos_tc),
  df_ciclos_combustibles %>% dplyr::select(fecha, gasoil_var      = gasoil_tc),
  df_ciclos_combustibles %>% dplyr::select(fecha, nafta_prem_var  = nafta_prem_tc),
  df_ciclos_combustibles %>% dplyr::select(fecha, nafta_tot_var   = nafta_tot_tc),
  df_vino_limpio         %>% dplyr::select(fecha, vino_var        = vino_tc),
  df_var_exp_tot         %>% dplyr::select(fecha, exp_total_var   = exp_total_tc),
  df_var_exp_moat        %>% dplyr::select(fecha, exp_moat_var    = exp_moat_tc),
  df_var_exp_moab        %>% dplyr::select(fecha, exp_moab_var    = exp_moab_tc),
  df_var_exp_moit        %>% dplyr::select(fecha, exp_moit_var    = exp_moit_tc),
  df_var_exp_prim        %>% dplyr::select(fecha, exp_prim_var    = exp_prim_tc),
  df_var_exp_comb        %>% dplyr::select(fecha, exp_comb_var    = exp_comb_tc),
  df_var_m2              %>% dplyr::select(fecha, m2_var          = m2_tc),
  df_var_caja_ahorro     %>% dplyr::select(fecha, caja_ahorro_var = caja_ahorro_tc),
  df_var_base_mon        %>% dplyr::select(fecha, base_mon_var    = base_mon_tc),
  df_var_circulacion     %>% dplyr::select(fecha, circulacion_var = circulacion_tc)
)

df_adelantadas_consolidado <- purrr::reduce(lista_df_adelantadas, dplyr::full_join, by = "fecha") %>%
  dplyr::arrange(fecha)

df_evaluacion_adelantadas <- df_adelantadas_consolidado %>%
  dplyr::mutate(across(-fecha, calc_variacion_simetrica)) %>%
  dplyr::inner_join(df_ics_target, by = "fecha")

lista_variables_adelantadas <- list(
  "Despachos de Cemento"          = "cemento_var",
  "ITCRM Mendoza"                 = "itcrm_var",
  "Comercio Automotor"            = "auto_var",
  "Ratio Préstamos / Depósitos"   = "ratio_var",
  "Motovehículos"                 = "moto_var",
  "Escrituras de Compraventa"     = "escrituras_var",
  "Petróleo Procesado (m³)"       = "petroleo_var",
  "Ocupación Hotelera (%)"        = "hotel_var",
  "Préstamos al Sector Privado"   = "prestamos_var",
  "Venta Gasoil Total (m³)"       = "gasoil_var",
  "Venta Nafta Premium (m³)"      = "nafta_prem_var",
  "Venta Naftas Totales (m³)"     = "nafta_tot_var",
  "Despachos de Vino (mhl)"       = "vino_var",
  "Exportaciones Totales (Tn)"    = "exp_total_var",
  "MOA Total (Tn)"                = "exp_moat_var",
  "MOA Bebidas (Tn)"              = "exp_moab_var",
  "MOI Total (Tn)"                = "exp_moit_var",
  "Productos Primarios (Tn)"      = "exp_prim_var",
  "Combustibles y Energía (Tn)"   = "exp_comb_var",
  "M2 Moneda Nacional Real"       = "m2_var",
  "Caja de Ahorro MN Real"        = "caja_ahorro_var",
  "Base Monetaria Total Real"     = "base_mon_var",
  "Circulación en Público Real"   = "circulacion_var"
)

# ------------------------------------------------------------------------------
# C. FUNCIONES DE CÁLCULO DE MÉTRICAS (CCF Y GRANGER)
# ------------------------------------------------------------------------------

obtener_metricas_adelantadas <- function(df_datos, col_variable, nombre_variable) {
  
  df_pair <- df_datos %>%
    dplyr::select(fecha, ics_target, all_of(col_variable)) %>%
    tidyr::drop_na()
  
  if (nrow(df_pair) < 15) {
    return(list(
      ccf = data.frame(`Variable Adelantada` = nombre_variable, check.names = FALSE),
      granger = data.frame(`Variable Adelantada` = nombre_variable, check.names = FALSE)
    ))
  }
  
  # 1. Correlación Cruzada (CCF: Lags -12 a +12 meses)
  ccf_obj <- ccf(df_pair[[col_variable]], df_pair$ics_target, lag.max = 12, plot = FALSE)
  lags <- ccf_obj$lag[, 1, 1]
  corrs <- ccf_obj$acf[, 1, 1]
  
  max_idx <- which.max(abs(corrs))
  lag_optimo <- lags[max_idx]
  max_r <- corrs[max_idx]
  r_lag0 <- corrs[lags == 0]
  
  df_ccf <- data.frame(
    `Variable Adelantada`   = nombre_variable,
    `Lag -12`               = round(corrs[lags == -12], 3),
    `Lag -6`                = round(corrs[lags == -6], 3),
    `Lag -3`                = round(corrs[lags == -3], 3),
    `Lag 0 (Coincidente)`   = round(r_lag0, 3),
    `Lag +3`                = round(corrs[lags == 3], 3),
    `Lag +6`                = round(corrs[lags == 6], 3),
    `Lag Óptimo`            = lag_optimo,
    `Max Correlación (|r|)` = round(max_r, 3),
    check.names = FALSE
  )
  
  # 2. Test de Causalidad de Granger (Lag 1 y Lag 2 mensuales) usando df_pair
  g1_fwd <- lmtest::grangertest(as.formula(paste("ics_target ~", col_variable)), order = 1, data = df_pair)
  g2_fwd <- lmtest::grangertest(as.formula(paste("ics_target ~", col_variable)), order = 2, data = df_pair)
  
  g1_rev <- lmtest::grangertest(as.formula(paste(col_variable, "~ ics_target")), order = 1, data = df_pair)
  g2_rev <- lmtest::grangertest(as.formula(paste(col_variable, "~ ics_target")), order = 2, data = df_pair)
  
  df_granger <- data.frame(
    `Variable Adelantada` = nombre_variable,
    `F1 (Var->ICS) L1`    = round(g1_fwd$F[2], 3),
    `p-val L1`            = round(g1_fwd$`Pr(>F)`[2], 4),
    `F2 (ICS->Var) L1`    = round(g1_rev$F[2], 3),
    `p-val Rev L1`        = round(g1_rev$`Pr(>F)`[2], 4),
    `F1 (Var->ICS) L2`    = round(g2_fwd$F[2], 3),
    `p-val L2`            = round(g2_fwd$`Pr(>F)`[2], 4),
    `F2 (ICS->Var) L2`    = round(g2_rev$F[2], 3),
    `p-val Rev L2`        = round(g2_rev$`Pr(>F)`[2], 4),
    check.names = FALSE
  )
  
  return(list(ccf = df_ccf, granger = df_granger))
}

# ------------------------------------------------------------------------------
# D. EJECUCIÓN E IMPRESIÓN DE TABLAS EN CONSOLA
# ------------------------------------------------------------------------------

resultados_metricas <- purrr::imap(lista_variables_adelantadas, ~ obtener_metricas_adelantadas(df_evaluacion_adelantadas, .x, .y))

res_ccf_tot     <- purrr::map_dfr(resultados_metricas, "ccf")
res_granger_tot <- purrr::map_dfr(resultados_metricas, "granger")

# Tabla A.1: Correlación Cruzada (CCF)
cat("\n========================================================================================================\n")
cat("          TABLA A.1: CORRELACIÓN CRUZADA (CCF) DE VARIABLES ADELANTADAS VS. ICS                          \n")
cat("========================================================================================================\n")
print(knitr::kable(res_ccf_tot, format = "simple", align = "lrrrrrrrr"))

# Tabla A.2: Test de Causalidad de Granger
cat("\n========================================================================================================\n")
cat("          TABLA A.2: TEST DE CAUSALIDAD DE GRANGER (VARIABLES ADELANTADAS VS. ICS)                       \n")
cat("========================================================================================================\n")
print(knitr::kable(res_granger_tot, format = "simple", align = "lrrrrrrrr"))

# ==============================================================================
# 6. ÍNDICE COMPUESTO ADELANTADO (ICA 4.2) - 4 COMPONENTES
# (Comercio Automotor, Motovehículos, Escrituras, Despachos de Cemento)
# ==============================================================================

# ------------------------------------------------------------------------------
# 6.1 CONSOLIDACIÓN Y CÁLCULO DE VARIACIONES SIMÉTRICAS (4 COMPONENTES)
# ------------------------------------------------------------------------------
lista_ica_series <- list(
  df_auto_limpio %>% select(fecha, auto_tc),
  df_moto_limpio %>% select(fecha, moto_tc),
  df_escrituras_limpio %>% select(fecha, escrituras_tc),
  df_cemento_completo %>% select(fecha, cemento_tc)
)

df_ica_series <- purrr::reduce(lista_ica_series, inner_join, by = "fecha") %>%
  arrange(fecha) %>%
  mutate(
    anio           = year(fecha),
    auto_sym       = calc_variacion_simetrica(auto_tc),
    moto_sym       = calc_variacion_simetrica(moto_tc),
    escrituras_sym = calc_variacion_simetrica(escrituras_tc),
    cemento_sym    = calc_variacion_simetrica(cemento_tc)
  )

# ------------------------------------------------------------------------------
# 6.2 PONDERACIÓN NBER / TCB POR AMPLITUD INVERSA DE VOLATILIDAD
# ------------------------------------------------------------------------------
df_volatilidad_ica <- df_ica_series %>% 
  select(auto_sym, moto_sym, escrituras_sym, cemento_sym) %>% 
  drop_na()

std_devs_ica <- sapply(df_volatilidad_ica, sd)
inv_vol_ica  <- 1 / std_devs_ica
weights_ica  <- inv_vol_ica / sum(inv_vol_ica)

df_ponderadores_ica <- data.frame(
  Variable       = c("Comercio Automotor", "Motovehículos", "Escrituras de Compraventa", "Despachos de Cemento"),
  Desviacion_Std = round(std_devs_ica, 4), 
  Inverso_Vol    = round(inv_vol_ica, 4),
  Ponderador     = round(weights_ica, 4), 
  Porcentaje     = paste0(round(weights_ica * 100, 2), "%")
)

cat("\n==================================================================\n")
cat(" TABLA DE PONDERADORES DEL ÍNDICE COMPUESTO ADELANTADO (ICA 4.2) \n")
cat("==================================================================\n")
print(knitr::kable(df_ponderadores_ica, col.names = c("Componente Adelantado", "Desv. Estándar (c_i)", "Amplitud Inversa (1/c_i)", "Ponderador (w_i)", "Peso Relativo (%)"), align = "c"))

# ------------------------------------------------------------------------------
# 6.3 TASA SINTÉTICA Y ENCADENAMIENTO RECURSIVO (BASE 2010 = 100)
# ------------------------------------------------------------------------------
df_ica_series <- df_ica_series %>%
  mutate(
    r_adelantado = ifelse(
      is.na(auto_sym) | is.na(cemento_sym), NA_real_,
      as.numeric(unname(weights_ica["auto_sym"]))       * auto_sym +
        as.numeric(unname(weights_ica["moto_sym"]))       * moto_sym +
        as.numeric(unname(weights_ica["escrituras_sym"])) * escrituras_sym +
        as.numeric(unname(weights_ica["cemento_sym"]))    * cemento_sym
    )
  )

n_obs_ica <- nrow(df_ica_series)
idx_ica <- numeric(n_obs_ica)
idx_start_ica <- which(!is.na(df_ica_series$r_adelantado))[1]

if(length(idx_start_ica) > 0 && !is.na(idx_start_ica)) {
  idx_ica[1:(idx_start_ica - 1)] <- NA
  idx_ica[idx_start_ica - 1]     <- 100
  for (t in idx_start_ica:n_obs_ica) {
    r_t <- df_ica_series$r_adelantado[t]
    idx_ica[t] <- idx_ica[t - 1] * (200 + r_t) / (200 - r_t)
  }
} else {
  idx_ica[] <- NA
}

df_ica_series$indice_adelantado_raw <- idx_ica
base_2010_ica <- mean(df_ica_series$indice_adelantado_raw[df_ica_series$anio == 2010], na.rm = TRUE)

df_ica_series <- df_ica_series %>%
  mutate(
    indice_adelantado = (indice_adelantado_raw / base_2010_ica) * 100,
    ica_tc            = indice_adelantado
  )

# ------------------------------------------------------------------------------
# 6.4 FILTRO HODRICK-PRESCOTT Y BRY-BOSCHAN SOBRE EL ICA (4 Comp.)
# ------------------------------------------------------------------------------
ica_no_na <- df_ica_series$indice_adelantado[!is.na(df_ica_series$indice_adelantado)]

if (length(ica_no_na) > 0) {
  ica_ts_m <- ts(ica_no_na, start = c(2010, 1), frequency = 12)
  hp_ica_m <- mFilter::hpfilter(ica_ts_m, freq = 14400, type = "lambda")
  df_ica_series$ica_suave_hp <- NA_real_
  df_ica_series$ica_suave_hp[!is.na(df_ica_series$indice_adelantado)] <- as.numeric(hp_ica_m$trend)
} else {
  df_ica_series$ica_suave_hp <- NA_real_
}

pg_ica_tc <- bry_boschan_nber(df_ica_series %>% filter(!is.na(ica_tc)), col_y = "ica_tc")

df_plot_bb_ica <- preparar_pg_plot(as.data.frame(df_ica_series), pg_ica_tc)

plot_bb_ica_tc <- graficar_bry_boschan(
  df_plot = df_plot_bb_ica,
  col_tc_orig = "ica_tc", 
  col_tc_hp = "ica_suave_hp", 
  titulo_serie = "Índice Compuesto Adelantado (ICA 4.2)", 
  y_label = "Índice (Base 2010 = 100)", 
  color_serie = if (exists("col_ica")) col_ica else "#E69F00"
)
print(plot_bb_ica_tc)

if (nrow(pg_ica_tc) > 0) {
  audit_ica <- auditar_tiempos_bb(pg_ica_tc, df_serie = as.data.frame(df_ica_series))
}

# ==============================================================================
# 6.5 PUNTOS DE GIRO COMPARADOS (ICS VS. ICA 4.2)
# ==============================================================================
library(ggplot2)
library(dplyr)

if("Fecha" %in% names(df_series_mensual) && !"fecha" %in% names(df_series_mensual)) {
  df_series_mensual$fecha <- df_series_mensual$Fecha
}

asegurar_pg_valido <- function(pg, es_ica = FALSE) {
  if (is.null(pg) || !is.data.frame(pg) || nrow(pg) == 0) {
    return(data.frame(fecha = as.Date(character()), Valor = numeric(), Etiqueta_Giro = character()))
  }
  etiqueta_sufijo <- ifelse(es_ica, " (ICA)", " (ICS)")
  pg <- pg %>% mutate(Etiqueta_Giro = paste0(ifelse(Tipo == "Peak", "Pico", "Valle"), etiqueta_sufijo))
  if("Fecha" %in% names(pg)) pg <- pg %>% rename(fecha = Fecha)
  return(pg)
}

if (!exists("pg_ics_tc") || is.null(pg_ics_tc)) {
  pg_ics_tc <- bry_boschan_nber(df_series_mensual %>% filter(!is.na(ics_tc)), col_y = "ics_tc")
}

df_exp_comparacion <- df_series_mensual %>% 
  select(fecha, ics_tc, ics_suave_hp) %>% 
  inner_join(df_ica_series %>% select(fecha, ica_tc, ica_suave_hp), by = "fecha")

df_pg_combinados <- bind_rows(
  asegurar_pg_valido(pg_ics_tc, es_ica = FALSE), 
  asegurar_pg_valido(pg_ica_tc, es_ica = TRUE)
)


# ------------------------------------------------------------------------------
# GRÁFICO 1: Comparativo sobre serie TC SIN marcado BB
# ------------------------------------------------------------------------------
plot_1_tc_limpia <- ggplot(data = df_exp_comparacion, aes(x = fecha)) +
  geom_line(aes(y = ics_tc, color = "ICS"), linewidth = 1.1) +
  geom_line(aes(y = ica_tc, color = "ICA"), linewidth = 1.1) +
  scale_color_manual(
    name = NULL,
    values = c("ICS" = col_ics, "ICA" = if(exists("col_ica")) col_ica else "#E69F00")
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_exp_comparacion$fecha, na.rm = TRUE), max(df_exp_comparacion$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL, 
    x = NULL, y = "Índice (Base 2010 = 100)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(plot.title = element_text(face = "bold", hjust = 0.5), plot.subtitle = element_text(hjust = 0.5), legend.position = "bottom",
        panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
        plot.margin = margin(t = 10, r = 15, b = 10, l = 15))

print(plot_1_tc_limpia)


# ------------------------------------------------------------------------------
# GRÁFICO 2: Comparativo sobre serie TC CON marcado BB
# ------------------------------------------------------------------------------
plot_2_tc_con_bb <- ggplot(data = df_exp_comparacion, aes(x = fecha)) +
  geom_line(aes(y = ics_tc, color = "ICS (TC)"), linewidth = 1.1) +
  geom_line(aes(y = ica_tc, color = "ICA (TC)"), linewidth = 1.1) +
  {if(nrow(df_pg_combinados) > 0) geom_point(data = df_pg_combinados, aes(x = fecha, y = Valor, color = Etiqueta_Giro, shape = Etiqueta_Giro), size = 3.5)} +
  scale_color_manual(
    name = "Referencias",
    values = c("ICS (TC)" = col_ics, "ICA (TC)" = if(exists("col_ica")) col_ica else "#E69F00", "Pico (ICS)" = "#0066CC", "Valle (ICS)" = "#000033", "Pico (ICA)" = "#FF3300", "Valle (ICA)" = "#228B22"),
    breaks = c("ICS (TC)", "ICA (TC)", "Pico (ICS)", "Valle (ICS)", "Pico (ICA)", "Valle (ICA)")
  ) +
  scale_shape_manual(
    name = "Referencias",
    values = c("ICS (TC)" = NA, "ICA (TC)" = NA, "Pico (ICS)" = 17, "Valle (ICS)" = 25, "Pico (ICA)" = 17, "Valle (ICA)" = 25),
    breaks = c("ICS (TC)", "ICA (TC)", "Pico (ICS)", "Valle (ICS)", "Pico (ICA)", "Valle (ICA)")
  ) +
  guides(color = guide_legend(override.aes = list(linetype = c("solid", "solid", "blank", "blank", "blank", "blank"), shape = c(NA, NA, 17, 25, 17, 25))), shape = "none") +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_exp_comparacion$fecha, na.rm = TRUE), max(df_exp_comparacion$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "Índice (Base 2010 = 100)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(plot.title = element_text(face = "bold", hjust = 0.5), plot.subtitle = element_text(hjust = 0.5), legend.position = "bottom",
        panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
        plot.margin = margin(t = 10, r = 15, b = 10, l = 15))

print(plot_2_tc_con_bb)


# ------------------------------------------------------------------------------
# GRÁFICO 3: Comparativo sobre serie HP SIN marcado BB
# ------------------------------------------------------------------------------
plot_3_hp_limpia <- ggplot(data = df_exp_comparacion, aes(x = fecha)) +
  geom_line(aes(y = ics_suave_hp, color = "ICS (HP)"), linewidth = 1.3) +
  geom_line(aes(y = ica_suave_hp, color = "ICA (HP)"), linewidth = 1.3) +
  scale_color_manual(
    name = "Índice Suavizado",
    values = c("ICS (HP)" = col_ics, "ICA (HP)" = if(exists("col_ica")) col_ica else "#E69F00")
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_exp_comparacion$fecha, na.rm = TRUE), max(df_exp_comparacion$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "Índice (Base 2010 = 100)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(plot.title = element_text(face = "bold", hjust = 0.5), plot.subtitle = element_text(hjust = 0.5), legend.position = "bottom",
        panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
        plot.margin = margin(t = 10, r = 15, b = 10, l = 15))

print(plot_3_hp_limpia)

# ------------------------------------------------------------------------------
# GRÁFICO 4: Comparativo Integral (HP a color + TC en gris + marcado BB sobre TC)
# ------------------------------------------------------------------------------
plot_4_integral <- ggplot(data = df_exp_comparacion, aes(x = fecha)) +
  geom_line(aes(y = ics_tc, color = "ICS (TC Gris)"), linewidth = 0.6, alpha = 0.6) +
  geom_line(aes(y = ica_tc, color = "ICA (TC Gris)"), linewidth = 0.6, alpha = 0.6) +
  
  geom_line(aes(y = ics_suave_hp, color = "ICS (HP Color)"), linewidth = 1.2) +
  geom_line(aes(y = ica_suave_hp, color = "ICA (HP Color)"), linewidth = 1.2) +
  
  {if(nrow(df_pg_combinados) > 0) geom_point(data = df_pg_combinados, aes(x = fecha, y = Valor, color = Etiqueta_Giro, shape = Etiqueta_Giro), size = 3.5)} +
  
  scale_color_manual(
    name = "Referencias Generales",
    values = c(
      "ICS (HP Color)" = col_ics,   "ICA (HP Color)" = if(exists("col_ica")) col_ica else "#E69F00", 
      "ICS (TC Gris)"  = "gray55",  "ICA (TC Gris)"  = "gray75",
      "Pico (ICS)"     = "#0066CC", "Valle (ICS)"    = "#000033", 
      "Pico (ICA)"     = "#FF3300", "Valle (ICA)"    = "#228B22"
    ),
    breaks = c("ICS (HP Color)", "ICA (HP Color)", "ICS (TC Gris)", "ICA (TC Gris)", "Pico (ICS)", "Valle (ICS)", "Pico (ICA)", "Valle (ICA)")
  ) +
  scale_shape_manual(
    name = "Referencias Generales",
    values = c(
      "ICS (HP Color)" = NA, "ICA (HP Color)" = NA, 
      "ICS (TC Gris)"  = NA, "ICA (TC Gris)"  = NA,
      "Pico (ICS)"     = 17, "Valle (ICS)"    = 25, 
      "Pico (ICA)"     = 17, "Valle (ICA)"    = 25
    ),
    breaks = c("ICS (HP Color)", "ICA (HP Color)", "ICS (TC Gris)", "ICA (TC Gris)", "Pico (ICS)", "Valle (ICS)", "Pico (ICA)", "Valle (ICA)")
  ) +
  guides(
    color = guide_legend(
      nrow = 2, byrow = TRUE,
      override.aes = list(
        linetype  = c("solid", "solid", "solid", "solid", "blank", "blank", "blank", "blank"),
        linewidth = c(1.2, 1.2, 0.6, 0.6, NA, NA, NA, NA),
        shape     = c(NA, NA, NA, NA, 17, 25, 17, 25)
      )
    ), 
    shape = "none"
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_exp_comparacion$fecha, na.rm = TRUE), max(df_exp_comparacion$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL, 
    subtitle = NULL, 
    x = NULL, y = "Índices (Base 2010 = 100)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(plot.title = element_text(face = "bold", hjust = 0.5), plot.subtitle = element_text(hjust = 0.5), legend.position = "bottom",
        panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
        plot.margin = margin(t = 10, r = 15, b = 10, l = 15))

print(plot_4_integral)

# ==============================================================================
# 6.6 EVALUACIÓN GLOBAL (GRANGER Y CCF: ICS vs ICA 4.2)
# ==============================================================================

df_eval_global <- df_series_mensual %>%
  select(fecha, ics_tc) %>%
  inner_join(df_ica_series %>% select(fecha, r_ica = r_adelantado), by = "fecha") %>%
  arrange(fecha) %>%
  mutate(
    r_ics = 200 * (ics_tc - lag(ics_tc)) / (ics_tc + lag(ics_tc))
  ) %>%
  filter(!is.na(r_ics) & !is.na(r_ica))

# ------------------------------------------------------------------------------
# 1. TEST DE CAUSALIDAD DE GRANGER (Lags 1 a 12 usando purrr)
# ------------------------------------------------------------------------------
res_granger_lags <- purrr::map_dfr(1:12, function(p) {
  g_fwd <- lmtest::grangertest(r_ics ~ r_ica, order = p, data = df_eval_global)
  g_rev <- lmtest::grangertest(r_ica ~ r_ics, order = p, data = df_eval_global)
  
  data.frame(
    Lag_Meses               = p,
    `F (ICA -> ICS)`        = round(g_fwd$F[2], 3),
    `p-val (ICA -> ICS)`    = round(g_fwd$`Pr(>F)`[2], 4),
    `Significativo (Directo)`= ifelse(g_fwd$`Pr(>F)`[2] < 0.05, "SÍ (p < 0.05)", "NO"),
    `F (ICS -> ICA)`        = round(g_rev$F[2], 3),
    `p-val (ICS -> ICA)`    = round(g_rev$`Pr(>F)`[2], 4),
    `Causalidad Inversa`    = ifelse(g_rev$`Pr(>F)`[2] < 0.05, "DETECTADA", "NO (Exógeno)"),
    check.names             = FALSE
  )
})

cat("\n========================================================================================\n")
cat(" TEST DE CAUSALIDAD DE GRANGER BIDIRECCIONAL (LAG 1 A LAG 12) (ICA 4.2)\n")
cat("========================================================================================\n")
print(knitr::kable(res_granger_lags, align = "c"))

# ------------------------------------------------------------------------------
# 2. TEST DE CORRELACIÓN CRUZADA (CCF) TABULADO
# ------------------------------------------------------------------------------
ccf_obj_global <- ccf(df_eval_global$r_ica, df_eval_global$r_ics, lag.max = 12, plot = FALSE)
lags_g  <- ccf_obj_global$lag[, 1, 1]
corrs_g <- ccf_obj_global$acf[, 1, 1]

max_idx_g    <- which.max(abs(corrs_g))
lag_optimo_g <- lags_g[max_idx_g]
max_r_g      <- corrs_g[max_idx_g]
r_lag0_g     <- corrs_g[lags_g == 0]

df_ccf_ica <- data.frame(
  `Índice Evaluado`       = "ICA (4.2)",
  `Lag -12`               = round(corrs_g[lags_g == -12], 3),
  `Lag -6`                = round(corrs_g[lags_g == -6], 3),
  `Lag -3`                = round(corrs_g[lags_g == -3], 3),
  `Lag -1`                = round(corrs_g[lags_g == -1], 3),
  `Lag 0 (Coincidente)`   = round(r_lag0_g, 3),
  `Lag +1`                = round(corrs_g[lags_g == 1], 3),
  `Lag +3`                = round(corrs_g[lags_g == 3], 3),
  `Lag +6`                = round(corrs_g[lags_g == 6], 3),
  `Lag Óptimo`            = lag_optimo_g,
  `Max Correlación (|r|)` = round(max_r_g, 3),
  check.names = FALSE
)

cat("\n========================================================================================\n")
cat(" TABLA: CORRELACIÓN CRUZADA (CCF) - ICA (4.2) VS. ICS\n")
cat(" Nota: Valores 'Lag' negativos indican que el ICA ADELANTA al ICS.\n")
cat("========================================================================================\n")
print(knitr::kable(df_ccf_ica, format = "simple", align = "c"))

# ------------------------------------------------------------------------------
# 3. CORRELACIÓN CRUZADA Y AUTOCORRELACIÓN SIMÉTRICA (FIGURA 4)
# ------------------------------------------------------------------------------
df_ccf <- data.frame(Lag = ccf_obj_global$lag[, 1, 1], r = ccf_obj_global$acf[, 1, 1], Serie = "ICA (4.2)")

acf_ics_pos <- acf(df_eval_global$r_ics, lag.max = 12, plot = FALSE)
r_ics_sym   <- c(rev(acf_ics_pos$acf[-1, 1, 1]), acf_ics_pos$acf[, 1, 1])

df_acf <- data.frame(Lag = seq(-12, 12, by = 1), r = r_ics_sym, Serie = "ICS (Variable de Referencia)")

df_fig4 <- bind_rows(df_ccf, df_acf)

df_ica_only <- df_fig4 %>% filter(Serie == "ICA (4.2)")
idx_max     <- which.max(df_ica_only$r)
lag_max_ica <- df_ica_only$Lag[idx_max]
r_max_ica   <- df_ica_only$r[idx_max]

n_obs <- nrow(df_eval_global)
ci_95 <- 1.96 / sqrt(n_obs)

plot_figura4 <- ggplot(df_fig4, aes(x = Lag, y = r, color = Serie, linetype = Serie)) +
  geom_hline(yintercept = 0, color = "grey30", linewidth = 0.5) +
  geom_hline(yintercept = c(-ci_95, ci_95), linetype = "dotted", color = "grey50", linewidth = 0.6) +
  geom_point(size = 2.2, alpha = 0.85) +
  geom_smooth(method = "lm", formula = y ~ poly(x, 2, raw = TRUE), se = FALSE, linewidth = 1.2) +
  annotate("point", x = lag_max_ica, y = r_max_ica, color = "#D95F02", size = 4.5, shape = 18) +
  geom_vline(xintercept = lag_max_ica, linetype = "dashed", color = "#D95F02", linewidth = 0.5) +
  annotate("text", x = lag_max_ica - 2.5, y = r_max_ica + 0.06, 
           label = paste0("Lag Óptimo: ", lag_max_ica, " m\nr = ", round(r_max_ica, 3)),
           color = "#D95F02", fontface = "bold", size = 3.5) +
  scale_x_continuous(breaks = seq(-12, 12, by = 2), limits = c(-12, 12), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  scale_y_continuous(limits = c(-0.2, 1.1), breaks = seq(-0.2, 1.1, by = 0.2)) +
  scale_color_manual(values = c("ICA (4.2)" = "#D95F02", "ICS (Variable de Referencia)" = "#003366")) +
  scale_linetype_manual(values = c("ICA (4.2)" = "solid", "ICS (Variable de Referencia)" = "longdash")) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL, y = "Coeficiente de Correlación (r)", color = "Serie", linetype = "Serie"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title       = element_text(face = "bold", hjust = 0.5, size = 12),
    plot.subtitle    = element_text(hjust = 0.5, color = "grey30", size = 10, margin = margin(b = 10)),
    axis.title       = element_text(face = "bold"), legend.position  = "bottom",
    legend.title     = element_blank(), panel.grid.minor = element_blank(),
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_figura4)

# ------------------------------------------------------------------------------
# 0. PREPARACIÓN Y VERIFICACIÓN DE DATOS
# ------------------------------------------------------------------------------
if (!exists("df_eval_global")) {
  if (exists("df_ica_series") && exists("df_series_mensual")) {
    df_eval_global <- df_ica_series %>%
      select(fecha, ica_tc) %>%
      inner_join(
        df_series_mensual %>% select(fecha, ics_tc),
        by = "fecha"
      ) %>%
      filter(!is.na(ica_tc) & !is.na(ics_tc)) %>%
      arrange(fecha) %>%
      mutate(
        r_ica = 200 * (ica_tc - lag(ica_tc)) / (ica_tc + lag(ica_tc)),
        r_ics = 200 * (ics_tc - lag(ics_tc)) / (ics_tc + lag(ics_tc))
      ) %>%
      drop_na()
  } else if (exists("df_exp_comparacion")) {
    df_eval_global <- df_exp_comparacion %>%
      filter(!is.na(ica_tc) & !is.na(ics_tc)) %>%
      arrange(fecha) %>%
      mutate(
        r_ica = 200 * (ica_tc - lag(ica_tc)) / (ica_tc + lag(ica_tc)),
        r_ics = 200 * (ics_tc - lag(ics_tc)) / (ics_tc + lag(ics_tc))
      ) %>%
      drop_na()
  } else {
    stop("No se encontraron los data frames de insumo en memoria. Cargá df_ica_series y df_series_mensual.")
  }
}

col_ics <- "#003366"  # ICS - Variable de Referencia
col_ica <- "#E69F00"  # ICA - Indicador Adelantado
col_acc <- "#C85200"  # Línea vertical de referencia

# ------------------------------------------------------------------------------
# 1. CÁLCULO DE COEFICIENTES (CCF ICA vs ICS y ACF ICS)
# ------------------------------------------------------------------------------

# A. Correlación Cruzada Bivariada: ccf(ICA, ICS)
# Lags negativos (k < 0) indican que el ICA antecede/adelanta al ICS.
ccf_obj <- ccf(df_eval_global$r_ica, df_eval_global$r_ics, lag.max = 12, plot = FALSE)

df_ccf <- data.frame(
  Lag = as.vector(ccf_obj$lag),
  r   = as.vector(ccf_obj$acf),
  Serie = "ICA (Indicador Adelantado)"
)

# B. Autocorrelación Simétrica de Referencia: acf(ICS)
acf_ics_pos <- acf(df_eval_global$r_ics, lag.max = 12, plot = FALSE)
r_ics_sym   <- c(rev(acf_ics_pos$acf[-1, 1, 1]), acf_ics_pos$acf[, 1, 1])

df_acf <- data.frame(
  Lag = seq(-12, 12, by = 1),
  r   = r_ics_sym,
  Serie = "ICS (Variable de Referencia)"
)

# Identificación del Lag Óptimo de Adelantamiento y Puntos Máximos
idx_max     <- which.max(df_ccf$r)
lag_optimo  <- df_ccf$Lag[idx_max]  # -1
r_max_ica   <- df_ccf$r[idx_max]    # ~0.474

df_maximos <- data.frame(
  Lag = c(0, lag_optimo),
  r   = c(1.0, r_max_ica),
  Serie = c("ICS (Variable de Referencia)", "ICA (Indicador Adelantado)")
)

# Bandas de confianza al 95%
n_obs <- nrow(df_eval_global)
ci_95 <- 1.96 / sqrt(n_obs)

label_eje_y <- "Coeficiente de Correlación (r)"
label_eje_x <- "Desfasajes en la serie del ICA (Lags k)"


# ==============================================================================
# SECCIÓN A: GRÁFICO 1 - ESTILIZADO ARMÓNICO (SOBRIO, SOLO PUNTOS MÁXIMOS)
# Ideal para el Cuerpo Principal de la Tesis (Capítulo IV)
# ==============================================================================

grid_lags <- seq(-12, 12, length.out = 300)

# Parábola ICS: Vértice forzado en (0, 1.0) -> (1 - r) = alpha * k^2
fit_ics_alpha <- lm((1 - r) ~ 0 + I(Lag^2), data = df_acf %>% filter(Lag != 0))
alpha_ics     <- coef(fit_ics_alpha)
df_ics_curva  <- data.frame(
  Lag = grid_lags, 
  r = 1 - alpha_ics * (grid_lags^2), 
  Serie = "ICS (Variable de Referencia)"
)

# Parábola ICA: Vértice forzado en (-1, r_max) -> (r_max - r) = beta * (k - lag_optimo)^2
fit_ica_beta  <- lm((r_max_ica - r) ~ 0 + I((Lag - lag_optimo)^2), data = df_ccf %>% filter(Lag != lag_optimo))
beta_ica      <- coef(fit_ica_beta)
df_ica_curva  <- data.frame(
  Lag = grid_lags, 
  r = r_max_ica - beta_ica * ((grid_lags - lag_optimo)^2), 
  Serie = "ICA (Indicador Adelantado)"
)

df_curvas_armonicas <- bind_rows(df_ics_curva, df_ica_curva)

g1_estilizado <- ggplot() +
  geom_hline(yintercept = 0, color = "grey30", linewidth = 0.5) +
  geom_hline(yintercept = c(-ci_95, ci_95), linetype = "dotted", color = "grey50", linewidth = 0.6) +
  
  geom_line(
    data = df_curvas_armonicas, 
    aes(x = Lag, y = r, color = Serie, linetype = Serie), 
    linewidth = 1.2
  ) +
  
  # Puntos máximos únicamente: (0, 1.0) para ICS y (-1, r_max) para ICA
  geom_point(
    data = df_maximos, 
    aes(x = Lag, y = r, color = Serie), 
    size = 3.2, show.legend = FALSE
  ) +
  
  scale_x_continuous(breaks = seq(-12, 12, by = 2)) +
  scale_y_continuous(limits = c(-0.2, 1.1), breaks = seq(-0.2, 1.1, by = 0.2)) +
  
  scale_color_manual(values = c("ICA (Indicador Adelantado)" = col_ica, 
                                "ICS (Variable de Referencia)" = col_ics)) +
  scale_linetype_manual(values = c("ICA (Indicador Adelantado)" = "solid", 
                                   "ICS (Variable de Referencia)" = "longdash")) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = label_eje_x,
    y = label_eje_y,
    color = NULL,
    linetype = NULL
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    axis.title       = element_text(face = "bold"),
    legend.position  = "bottom",
    panel.grid.minor = element_blank(),
    panel.border     = element_rect(color = "black", fill = NA, linewidth = 0.5),
    axis.ticks       = element_line(color = "black", linewidth = 0.5),
    axis.ticks.length = unit(0.15, "cm")
  )

print(g1_estilizado)


# ==============================================================================
# SECCIÓN B: GRÁFICO 2 - EXPLICATIVO MUESTRAL
# ==============================================================================

df_puntos_observados <- bind_rows(df_ccf, df_acf)

g2_explicativo <- ggplot(df_puntos_observados, aes(x = Lag, y = r, color = Serie, linetype = Serie)) +
  geom_hline(yintercept = 0, color = "grey40", linewidth = 0.5) +
  geom_hline(yintercept = c(-ci_95, ci_95), linetype = "dotted", color = "grey60", linewidth = 0.5) +
  
  geom_smooth(method = "lm", formula = y ~ poly(x, 2, raw = TRUE), se = FALSE, linewidth = 1.1) +
  
  geom_point(size = 2.3, alpha = 0.75) +
  
  geom_vline(xintercept = lag_optimo, linetype = "dashed", color = col_acc, linewidth = 0.6) +
  geom_point(data = df_maximos, aes(x = Lag, y = r, color = Serie), size = 3.5, show.legend = FALSE) +
  
  scale_x_continuous(breaks = seq(-12, 12, by = 2)) +
  scale_y_continuous(limits = c(-0.2, 1.1), breaks = seq(-0.2, 1.1, by = 0.2)) +
  
  scale_color_manual(values = c("ICA (Indicador Adelantado)" = col_ica, 
                                "ICS (Variable de Referencia)" = col_ics)) +
  scale_linetype_manual(values = c("ICA (Indicador Adelantado)" = "solid", 
                                   "ICS (Variable de Referencia)" = "longdash")) +
  labs(
    title = NULL,
    subtitle = NULL,
    x = label_eje_x,
    y = label_eje_y,
    color = NULL,
    linetype = NULL
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    axis.title       = element_text(face = "bold"),
    legend.position  = "bottom",
    panel.grid.minor = element_blank(),
    panel.border     = element_rect(color = "black", fill = NA, linewidth = 0.5),
    axis.ticks       = element_line(color = "black", linewidth = 0.5),
    axis.ticks.length = unit(0.15, "cm")
  )

print(g2_explicativo)

# ==============================================================================
# SECCIÓN C: TABLA DE COEFICIENTES r(k) PARA k EN [-12, +12]
# ==============================================================================

df_tabla_r <- df_ccf %>%
  select(Lag, r_ICA = r) %>%
  inner_join(
    df_acf %>% select(Lag, r_ICS = r),
    by = "Lag"
  ) %>%
  mutate(
    r_ICA = round(r_ICA, 4),
    r_ICS = round(r_ICS, 4),
    Interpretacion = case_when(
      Lag < 0 & Lag == lag_optimo ~ paste0("¡MÁXIMO ADELANTO! (ICA adelanta ", abs(Lag), " mes)"),
      Lag < 0 ~ paste0("Adelanto del ICA (", abs(Lag), " meses)"),
      Lag == 0 ~ "Coincidente (Contemporáneo)",
      Lag > 0 ~ paste0("Rezago del ICA (", Lag, " meses)")
    )
  )

cat("\n==============================================================================\n")
cat(" TABLA DE CORRELACIÓN CRUZADA Y AUTOCORRELACIÓN: ICA VS. ICS (Lags -12 a +12)\n")
cat("==============================================================================\n\n")

print(
  knitr::kable(
    df_tabla_r,
    col.names = c("Lag (k)", "r (ICA vs ICS)", "r (Autocorrelación ICS)", "Interpretación Cíclica"),
    align = c("c", "r", "r", "l"),
    caption = "Tabla F.1. Coeficientes de Correlación Cruzada entre el ICA y el ICS"
  )
)

# ==============================================================================
# 7. CÁLCULO Y AUDITORÍA DEL ÍNDICE DE DIFUSIÓN (ICS: 5 COMP. | ICA: 4 COMP.)
# Metodología: Standard The Conference Board (TCB) / NBER
# Tratamiento: Filtro Hodrick-Prescott (lambda = 14.400) sobre componentes TC
# ==============================================================================

theme_set(theme_minimal(base_size = 10, base_family = "sans"))

# ------------------------------------------------------------------------------
# 7.0 FUNCIONES BASE DEL ÍNDICE DE DIFUSIÓN Y TRAYECTORIA ENVOLVENTE
# ------------------------------------------------------------------------------

detectar_col_fecha <- function(df) {
  if ("fecha" %in% names(df)) return("fecha")
  if ("Fecha" %in% names(df)) return("Fecha")
  stop("El dataframe no contiene una columna 'fecha' ni 'Fecha'.")
}

preparar_series_hp_difusion <- function(df_input, cols_vars_tc) {
  col_fecha_exacta <- detectar_col_fecha(df_input)
  cols_existentes  <- intersect(cols_vars_tc, colnames(df_input))
  
  df_proc <- df_input %>%
    select(all_of(col_fecha_exacta), all_of(cols_existentes)) %>%
    arrange(.data[[col_fecha_exacta]])
  
  for (col in cols_existentes) {
    serie_vec <- df_proc[[col]]
    if (any(is.na(serie_vec))) {
      serie_vec <- zoo::na.locf(zoo::na.locf(serie_vec, na.rm = FALSE), fromLast = TRUE)
    }
    hp_res <- mFilter::hpfilter(serie_vec, freq = 14400, type = "lambda")
    df_proc[[paste0(col, "_hp")]] <- as.numeric(hp_res$trend)
  }
  
  return(df_proc)
}

calcular_difusion_intermensual <- function(df_hp_input, cols_vars_hp) {
  col_fecha_exacta <- detectar_col_fecha(df_hp_input)
  cols_existentes  <- intersect(cols_vars_hp, colnames(df_hp_input))
  K <- length(cols_existentes)
  
  df_direcciones <- df_hp_input %>%
    select(all_of(col_fecha_exacta), all_of(cols_existentes)) %>%
    arrange(.data[[col_fecha_exacta]]) %>%
    mutate(across(
      .cols = all_of(cols_existentes),
      .fns = function(x) {
        x_lag1 <- lag(x, 1)
        case_when(
          is.na(x_lag1) ~ NA_real_,
          x > x_lag1    ~ 1.0,
          x == x_lag1   ~ 0.5,
          x < x_lag1    ~ 0.0
        )
      },
      .names = "d1_{.col}"
    ))
  
  cols_d1 <- paste0("d1_", cols_existentes)
  
  df_difusion <- df_direcciones %>%
    rowwise() %>%
    mutate(
      R_t         = sum(c_across(all_of(cols_d1)) == 1.0, na.rm = TRUE),
      r_t         = sum(c_across(all_of(cols_d1)) == 0.5, na.rm = TRUE),
      C_t         = sum(c_across(all_of(cols_d1)) == 0.0, na.rm = TRUE),
      suma_scores = sum(c_across(all_of(cols_d1)), na.rm = TRUE),
      DI_t        = ifelse(is.na(c_across(all_of(cols_d1))[1]), NA_real_, (suma_scores / K) * 100)
    ) %>%
    ungroup() %>%
    select(fecha = all_of(col_fecha_exacta), all_of(cols_d1), R_t, r_t, C_t, DI_t)
  
  return(df_difusion)
}

calcular_difusion_6m_matriz <- function(df_hp_input, cols_vars_hp) {
  col_fecha_exacta <- detectar_col_fecha(df_hp_input)
  cols_existentes  <- intersect(cols_vars_hp, colnames(df_hp_input))
  
  df_span_6m <- df_hp_input %>%
    arrange(.data[[col_fecha_exacta]]) %>%
    mutate(across(
      .cols = all_of(cols_existentes),
      .fns = function(x) {
        val_lag6 <- lag(x, 6)
        case_when(
          is.na(val_lag6) ~ NA_real_,
          x > val_lag6    ~ 1.0,
          x == val_lag6   ~ 0.5,
          x < val_lag6    ~ 0.0
        )
      },
      .names = "d6_{.col}"
    )) %>%
    rename(fecha = all_of(col_fecha_exacta))
  
  return(df_span_6m)
}

generar_tabla_envolvente_difusion <- function(df_puntos_giro, df_difusion, df_sintetico, col_sintetico) {
  if (is.null(df_puntos_giro) || nrow(df_puntos_giro) == 0) {
    return(data.frame(Mensaje = "Sin puntos de giro detectados para evaluar trayectoria envolvente."))
  }
  
  col_fecha_pg  <- detectar_col_fecha(df_puntos_giro)
  col_fecha_s   <- detectar_col_fecha(df_sintetico)
  
  cols_components <- grep("^(d1_|d6_)", colnames(df_difusion), value = TRUE)
  N <- length(cols_components)
  
  if (N == 0) stop("Error: No se encontraron columnas de estados discretos (d1_ o d6_) en df_difusion.")
  
  df_di_recalculado <- df_difusion %>%
    select(fecha, all_of(cols_components)) %>%
    rowwise() %>%
    mutate(
      DI_t_recalc = (sum(c_across(all_of(cols_components)), na.rm = TRUE) / N) * 100
    ) %>%
    ungroup() %>%
    select(fecha, DI_t_recalc)
  
  df_giros <- df_puntos_giro %>%
    select(fecha = .data[[col_fecha_pg]], Tipo_Giro = Tipo) %>%
    left_join(df_sintetico %>% select(fecha = .data[[col_fecha_s]], Nivel_Sintetico_t0 = .data[[col_sintetico]]), by = "fecha")
  
  df_ventana <- df_giros %>%
    mutate(
      Fecha_m6 = fecha %m-% months(6),
      Fecha_m3 = fecha %m-% months(3),
      Fecha_m1 = fecha %m-% months(1),
      Fecha_t0 = fecha,
      Fecha_p1 = fecha %m+% months(1),
      Fecha_p3 = fecha %m+% months(3),
      Fecha_p6 = fecha %m+% months(6)
    )
  
  df_envolvente <- df_ventana %>%
    left_join(df_di_recalculado %>% rename(DI_m6 = DI_t_recalc), by = c("Fecha_m6" = "fecha")) %>%
    left_join(df_di_recalculado %>% rename(DI_m3 = DI_t_recalc), by = c("Fecha_m3" = "fecha")) %>%
    left_join(df_di_recalculado %>% rename(DI_m1 = DI_t_recalc), by = c("Fecha_m1" = "fecha")) %>%
    left_join(df_di_recalculado %>% rename(DI_t0 = DI_t_recalc), by = c("Fecha_t0" = "fecha")) %>%
    left_join(df_di_recalculado %>% rename(DI_p1 = DI_t_recalc), by = c("Fecha_p1" = "fecha")) %>%
    left_join(df_di_recalculado %>% rename(DI_p3 = DI_t_recalc), by = c("Fecha_p3" = "fecha")) %>%
    left_join(df_di_recalculado %>% rename(DI_p6 = DI_t_recalc), by = c("Fecha_p6" = "fecha")) %>%
    mutate(
      Fecha_Giro         = format(fecha, "%Y-%m"),
      Nivel_Sintetico_t0 = round(Nivel_Sintetico_t0, 2),
      `t-6`              = ifelse(is.na(DI_m6), "-", paste0(round(DI_m6, 1), "%")),
      `t-3`              = ifelse(is.na(DI_m3), "-", paste0(round(DI_m3, 1), "%")),
      `t-1`              = ifelse(is.na(DI_m1), "-", paste0(round(DI_m1, 1), "%")),
      `t0`               = ifelse(is.na(DI_t0), "-", paste0(round(DI_t0, 1), "%")),
      `t+1`              = ifelse(is.na(DI_p1), "-", paste0(round(DI_p1, 1), "%")),
      `t+3`              = ifelse(is.na(DI_p3), "-", paste0(round(DI_p3, 1), "%")),
      `t+6`              = ifelse(is.na(DI_p6), "-", paste0(round(DI_p6, 1), "%"))
    ) %>%
    select(Fecha_Giro, Tipo_Giro, Nivel_Sintetico_t0, `t-6`, `t-3`, `t-1`, `t0`, `t+1`, `t+3`, `t+6`)
  
  return(df_envolvente)
}

auditar_componentes_envolvente <- function(df_puntos_giro, df_span_6m, cols_vars_hp) {
  if (is.null(df_puntos_giro) || nrow(df_puntos_giro) == 0) {
    return(data.frame(Mensaje = "Sin puntos de giro detectados para evaluar componentes."))
  }
  
  col_fecha_pg <- detectar_col_fecha(df_puntos_giro)
  cols_d6 <- paste0("d6_", intersect(cols_vars_hp, gsub("d6_", "", colnames(df_span_6m))))
  
  giros_fechas <- df_puntos_giro %>% 
    select(fecha = .data[[col_fecha_pg]], Tipo_Giro = Tipo)
  
  lista_resultados <- list()
  
  for (i in seq_len(nrow(giros_fechas))) {
    f_t0 <- giros_fechas$fecha[i]
    tipo <- giros_fechas$Tipo_Giro[i]
    
    fechas_eval <- c(
      f_t0 %m-% months(6), f_t0 %m-% months(3), f_t0 %m-% months(1),
      f_t0,
      f_t0 %m+% months(1), f_t0 %m+% months(3), f_t0 %m+% months(6)
    )
    etiquetas <- c("t-6", "t-3", "t-1", "t0", "t+1", "t+3", "t+6")
    
    sub_t <- df_span_6m %>%
      filter(fecha %in% fechas_eval) %>%
      mutate(
        Punto_Giro = paste0(format(f_t0, "%Y-%m"), " (", tipo, ")"),
        Horizonte  = factor(etiquetas[match(fecha, fechas_eval)], levels = etiquetas)
      ) %>%
      arrange(Horizonte) %>%
      select(Punto_Giro, Horizonte, fecha, all_of(cols_d6))
    
    lista_resultados[[i]] <- sub_t
  }
  
  return(bind_rows(lista_resultados))
}

graficar_difusion_independiente <- function(df_difusion, df_puntos_giro, titulo_indicador, col_linea = "#003366") {
  col_fecha_dif <- detectar_col_fecha(df_difusion)
  
  df_plot <- df_difusion %>%
    filter(!is.na(DI_t)) %>%
    rename(fecha = .data[[col_fecha_dif]])
  
  p <- ggplot(df_plot, aes(x = fecha, y = DI_t)) +
    geom_ribbon(aes(ymin = 50, ymax = pmax(DI_t, 50)), fill = "#228B22", alpha = 0.25) +
    geom_ribbon(aes(ymin = pmin(DI_t, 50), ymax = 50), fill = "#FF3300", alpha = 0.25) +
    geom_hline(yintercept = 50, linetype = "dashed", color = "#D9534F", linewidth = 0.8)
  
  if (!is.null(df_puntos_giro) && nrow(df_puntos_giro) > 0) {
    col_fecha_pg  <- detectar_col_fecha(df_puntos_giro)
    giros_picos  <- df_puntos_giro %>% filter(Tipo == "Peak")
    giros_valles <- df_puntos_giro %>% filter(Tipo == "Trough")
    
    if (nrow(giros_picos) > 0) p <- p + geom_vline(data = giros_picos, aes(xintercept = .data[[col_fecha_pg]]), linetype = "dotdash", color = "red", linewidth = 0.7, alpha = 0.85)
    if (nrow(giros_valles) > 0) p <- p + geom_vline(data = giros_valles, aes(xintercept = .data[[col_fecha_pg]]), linetype = "dotdash", color = "green4", linewidth = 0.7, alpha = 0.85)
  }
  
  p <- p + 
    geom_line(color = col_linea, linewidth = 0.9) +
    geom_point(color = col_linea, size = 1.2) +
    scale_y_continuous(limits = c(0, 100), breaks = seq(0, 100, 25), labels = function(x) paste0(x, "%")) +
    scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_plot$fecha, na.rm = TRUE), max(df_plot$fecha, na.rm = TRUE)), expand = c(0, 0)) +
    coord_cartesian(clip = "off") +
    labs(
      title    = NULL,
      subtitle = NULL,
      x        = NULL, 
      y        = "Difusión (%)"
    ) +
    theme_minimal(base_size = 10, base_family = "sans") +
    theme(
      plot.title    = element_text(face = "bold", hjust = 0.5),
      plot.subtitle = element_text(hjust = 0.5, size = 8.5),
      panel.grid.minor = element_blank(),
      panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
      plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
    )
  
  return(p)
}

# ==============================================================================
# 7.1 ÍNDICE DE DIFUSIÓN DEL ÍNDICE COINCIDENTE SINTÉTICO (ICS) - 5 COMPONENTES
# ==============================================================================

vars_ics_tc <- c("remun_tc", "empleo_tc", "trib_tc", "centros_tc", "petroleo_tc")
vars_ics_hp_names <- paste0(vars_ics_tc, "_hp")

if ("petroleo_tc" %in% colnames(df_petroleo_limpio) && !"petroleo_tc" %in% colnames(df_series_mensual)) {
  col_fecha_petroleo <- detectar_col_fecha(df_petroleo_limpio)
  col_fecha_series   <- detectar_col_fecha(df_series_mensual)
  
  df_series_mensual <- df_series_mensual %>%
    left_join(
      df_petroleo_limpio %>% select(all_of(col_fecha_petroleo), petroleo_tc) %>% rename(fecha = all_of(col_fecha_petroleo)), 
      by = setNames("fecha", col_fecha_series)
    )
}

df_ics_hp_prep         <- preparar_series_hp_difusion(df_series_mensual, cols_vars_tc = vars_ics_tc)
df_di_ics_intermensual <- calcular_difusion_intermensual(df_ics_hp_prep, cols_vars_hp = vars_ics_hp_names)
df_di_ics_6m_matriz    <- calcular_difusion_6m_matriz(df_ics_hp_prep, cols_vars_hp = vars_ics_hp_names)

if (!exists("pg_ics_tc") || is.null(pg_ics_tc) || !is.data.frame(pg_ics_tc) || nrow(pg_ics_tc) == 0) {
  if ("ics_tc" %in% names(df_series_mensual)) {
    df_valid_ics <- df_series_mensual %>% filter(!is.na(ics_tc))
    pg_ics_tc <- if(nrow(df_valid_ics) > 0) bry_boschan_nber(df_valid_ics, col_y = "ics_tc") else data.frame()
  } else {
    pg_ics_tc <- data.frame(fecha = as.Date(character()), Tipo = character(), Valor = numeric())
  }
}

tabla_envolvente_ics      <- generar_tabla_envolvente_difusion(pg_ics_tc, df_di_ics_6m_matriz, df_series_mensual, "ics_tc")
tabla_componentes_ics_env <- auditar_componentes_envolvente(pg_ics_tc, df_di_ics_6m_matriz, vars_ics_hp_names)

plot_difusion_ics <- graficar_difusion_independiente(
  df_difusion      = df_di_ics_intermensual, 
  df_puntos_giro   = pg_ics_tc, 
  titulo_indicador = "Índice Coincidente Sintético (ICS)", 
  col_linea        = if (exists("col_ics")) col_ics else "#003366"
)

cat("\n================================================================================================\n")
cat("   TRAYECTORIA ENVOLVENTE A 6 MESES (t-6 a t+6) - ÍNDICE COINCIDENTE SINTÉTICO (ICS)\n")
cat("================================================================================================\n")
print(knitr::kable(tabla_envolvente_ics, align = "c"))

cat("\n================================================================================================\n")
cat(" FLUCTUACIÓN A 6 MESES POR COMPONENTE DEL ICS EN VENTANA ENVOLVENTE \n")
cat("================================================================================================\n")
cols_nombres_ics <- c("Punto de Giro", "Horizonte", "Fecha", gsub("_tc_hp", "", intersect(vars_ics_hp_names, gsub("d6_", "", colnames(tabla_componentes_ics_env)))))
if(!("Mensaje" %in% names(tabla_componentes_ics_env))) {
  print(knitr::kable(tabla_componentes_ics_env, col.names = cols_nombres_ics, align = "c"))
} else {
  print(tabla_componentes_ics_env)
}

print(plot_difusion_ics)

# Auditoría de Tiempos Bry-Boschan para ICS
tabla_tiempos_ics <- auditar_tiempos_bb(pg_ics_tc, df_series_mensual)

cat("\n================================================================================================\n")
cat(" AUDITORÍA DE DURACIÓN DE FASES Y CICLOS BRY-BOSCHAN - ICS \n")
cat("================================================================================================\n")
print(knitr::kable(tabla_tiempos_ics, align = "c"))


# ==============================================================================
# 7.2 ÍNDICE DE DIFUSIÓN DEL ÍNDICE COMPUESTO ADELANTADO (ICA 4.2) - 4 COMPONENTES
# ==============================================================================

# Variables actualizadas: 4 componentes (Autos, Motos, Escrituras y Despachos de Cemento)
vars_ica_tc_4 <- c("auto_tc", "moto_tc", "escrituras_tc", "cemento_tc")
vars_ica_hp_names_4 <- paste0(vars_ica_tc_4, "_hp")

# Preparación y cálculo de matrices (4 Comp)
df_ica_hp_prep_4         <- preparar_series_hp_difusion(df_ica_series, cols_vars_tc = vars_ica_tc_4)
df_di_ica_intermensual_4 <- calcular_difusion_intermensual(df_ica_hp_prep_4, cols_vars_hp = vars_ica_hp_names_4)
df_di_ica_6m_matriz_4    <- calcular_difusion_6m_matriz(df_ica_hp_prep_4, cols_vars_hp = vars_ica_hp_names_4)

if (!exists("pg_ica_tc") || is.null(pg_ica_tc) || !is.data.frame(pg_ica_tc) || nrow(pg_ica_tc) == 0) {
  if ("ica_tc" %in% names(df_ica_series)) {
    df_valid_ica <- df_ica_series %>% filter(!is.na(ica_tc))
    pg_ica_tc <- if(nrow(df_valid_ica) > 0) bry_boschan_nber(df_valid_ica, col_y = "ica_tc") else data.frame()
  } else {
    pg_ica_tc <- data.frame(fecha = as.Date(character()), Tipo = character(), Valor = numeric())
  }
}

# Tablas ICA (A 6 Meses para Trayectoria y Desglose por Componente) - Usando pg_ica_tc
tabla_envolvente_ica_4      <- generar_tabla_envolvente_difusion(pg_ica_tc, df_di_ica_6m_matriz_4, df_ica_series, "ica_tc")
tabla_componentes_ica_env_4 <- auditar_componentes_envolvente(pg_ica_tc, df_di_ica_6m_matriz_4, vars_ica_hp_names_4)

# Gráfico ICA (Intermensual - 4 Comp)
plot_difusion_ica_4 <- graficar_difusion_independiente(
  df_difusion      = df_di_ica_intermensual_4, 
  df_puntos_giro   = pg_ica_tc, 
  titulo_indicador = "Índice Compuesto Adelantado (ICA 4.2 - 4 Comp.)", 
  col_linea        = if (exists("col_ica")) col_ica else "#E69F00"
)

cat("\n================================================================================================\n")
cat("   TRAYECTORIA ENVOLVENTE A 6 MESES (t-6 a t+6) - ÍNDICE COMPUESTO ADELANTADO (ICA 4.2)\n")
cat("================================================================================================\n")
print(knitr::kable(tabla_envolvente_ica_4, align = "c"))

cat("\n================================================================================================\n")
cat(" FLUCTUACIÓN A 6 MESES POR COMPONENTE DEL ICA 4.2 EN VENTANA ENVOLVENTE \n")
cat("================================================================================================\n")
cols_nombres_ica_4 <- c("Punto de Giro", "Horizonte", "Fecha", gsub("_tc_hp", "", intersect(vars_ica_hp_names_4, gsub("d6_", "", colnames(tabla_componentes_ica_env_4)))))
if(!("Mensaje" %in% names(tabla_componentes_ica_env_4))) {
  print(knitr::kable(tabla_componentes_ica_env_4, col.names = cols_nombres_ica_4, align = "c"))
} else {
  print(tabla_componentes_ica_env_4)
}

print(plot_difusion_ica_4)

# Auditoría de Tiempos Bry-Boschan para ICA (4 Comp)
tabla_tiempos_ica_4 <- auditar_tiempos_bb(pg_ica_tc, df_ica_series)

cat("\n================================================================================================\n")
cat(" AUDITORÍA DE DURACIÓN DE FASES Y CICLOS BRY-BOSCHAN - ICA 4.2 \n")
cat("================================================================================================\n")
print(knitr::kable(tabla_tiempos_ica_4, align = "c"))

# ==============================================================================
# EVALUACIÓN ESTANDARIZADA DE PROFUNDIDAD Y DURACIÓN (REGLA DE LAS 3 D DE TCB)
# ==============================================================================

library(dplyr)
library(ggplot2)
library(knitr)

# ------------------------------------------------------------------------------
# 1. CÁLCULO DE LA TASA DE VARIACIÓN ANUALIZADA A 6 MESES (TVA 6M)
# ------------------------------------------------------------------------------
calc_tva_6m <- function(x) {
  # Fórmula de Tasa Semestral Anualizada: ((x_t / x_{t-6})^2 - 1) * 100
  ((x / dplyr::lag(x, 6))^2 - 1) * 100
}

df_eval_tva <- df_exp_comparacion %>%
  mutate(
    tva_ics = calc_tva_6m(ics_tc),
    tva_ica = calc_tva_6m(ica_tc)
  )

# ------------------------------------------------------------------------------
# 2. GRÁFICO ESTANDARIZADO DE LA EVOLUCIÓN DE LA TVA (ICS VS. ICA)
# ------------------------------------------------------------------------------
plot_evolucion_tva <- ggplot(df_eval_tva, aes(x = fecha)) +
  # Línea neutral de cero y umbrales de profundidad TCB (+/- 2%)
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey30", linewidth = 0.8) +
  geom_hline(yintercept = c(-2, 2), linetype = "dotted", color = "grey50", linewidth = 0.6) +
  
  geom_line(aes(y = tva_ics, color = "ICS (Referencia)"), linewidth = 1.1) +
  geom_line(aes(y = tva_ica, color = "ICA (Adelantado)"), linewidth = 1.1) +
  
  scale_color_manual(
    name = NULL,
    values = c("ICS (Referencia)" = col_ics, "ICA (Adelantado)" = if(exists("col_ica")) col_ica else "#E69F00")
  ) +
  scale_x_date(
    date_breaks = "2 years", 
    date_labels = "%Y", 
    expand = expansion(mult = c(0.01, 0.03))
  ) +
  labs(
    title = NULL, subtitle = NULL, x = NULL,
    y = "TVA Semestral (%)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    legend.position = "bottom",
    panel.grid.minor = element_blank(),
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5),
    axis.ticks = element_line(color = "black", linewidth = 0.5),
    axis.ticks.length = unit(0.15, "cm")
  )

print(plot_evolucion_tva)

# ------------------------------------------------------------------------------
# 3. FUNCIÓN DE MATRIZ EN VENTANA ENVOLVENTE (t-6 a t+6) Y VALIDACIÓN DE PUNTOS
# ------------------------------------------------------------------------------
evaluar_puntos_giro_3d <- function(df_datos, df_pg, nombre_serie, col_tva, df_difusion = NULL) {
  if (is.null(df_pg) || !is.data.frame(df_pg) || nrow(df_pg) == 0) return(NULL)
  
  lista_filas <- list()
  
  for (i in 1:nrow(df_pg)) {
    f_giro <- df_pg$fecha[i]
    tipo   <- as.character(df_pg$Tipo[i])
    
    idx_t0 <- which(df_datos$fecha == f_giro)
    if (length(idx_t0) == 0) next
    
    get_val <- function(offset) {
      idx <- idx_t0 + offset
      if (idx >= 1 && idx <= nrow(df_datos)) {
        round(df_datos[[col_tva]][idx], 2)
      } else {
        NA
      }
    }
    
    tva_t0 <- get_val(0)
    tva_m6 <- get_val(-6)
    tva_m3 <- get_val(-3)
    tva_m1 <- get_val(-1)
    tva_p1 <- get_val(1)
    tva_p3 <- get_val(3)
    tva_p6 <- get_val(6)
    
    col_nivel <- if(grepl("ics", col_tva)) "ics_tc" else "ica_tc"
    niv_t0 <- df_datos[[col_nivel]][idx_t0]
    niv_m6 <- if(idx_t0 - 6 >= 1) df_datos[[col_nivel]][idx_t0 - 6] else NA
    
    ampl_6m <- if(!is.na(niv_m6) && niv_m6 != 0) round(100 * (niv_t0 - niv_m6) / niv_m6, 2) else NA
    
    id_t0 <- NA
    if (!is.null(df_difusion) && is.data.frame(df_difusion)) {
      col_f_dif <- if("fecha" %in% colnames(df_difusion)) "fecha" else colnames(df_difusion)[1]
      idx_dif <- which(df_difusion[[col_f_dif]] == f_giro)
      if (length(idx_dif) > 0 && "DI_t" %in% colnames(df_difusion)) {
        id_t0 <- round(df_difusion$DI_t[idx_dif], 1)
      }
    }
    
    cumple_depth <- if(!is.na(ampl_6m)) abs(ampl_6m) >= 1.5 else FALSE
    
    cumple_difusion <- if(!is.na(id_t0)) {
      if (tipo %in% c("Peak", "Pico")) id_t0 <= 50 else id_t0 >= 50
    } else TRUE
    
    dictamen <- if (cumple_depth && cumple_difusion) {
      "VALIDADO"
    } else if (!cumple_depth) {
      "DESCARTADO (Sin Profundidad)"
    } else {
      "DESCARTADO (Giro Concentrado)"
    }
    
    res_row <- data.frame(
      Serie = nombre_serie,
      Fecha_Giro = as.character(f_giro),
      Tipo = tipo,
      `t-6` = tva_m6,
      `t-3` = tva_m3,
      `t-1` = tva_m1,
      `t0` = tva_t0,
      `t+1` = tva_p1,
      `t+3` = tva_p3,
      `t+6` = tva_p6,
      `Ampl_6m (%)` = ampl_6m,
      `ID_t0 (%)` = id_t0,
      Dictamen = dictamen,
      check.names = FALSE,
      stringsAsFactors = FALSE
    )
    lista_filas[[i]] <- res_row
  }
  
  bind_rows(lista_filas)
}

# ------------------------------------------------------------------------------
# 4. EJECUCIÓN Y TABLA CONSOLIDADA CON OBJETOS REALES DE TU ENVIRONMENT
# ------------------------------------------------------------------------------
tabla_eval_ics <- evaluar_puntos_giro_3d(
  df_datos     = df_eval_tva, 
  df_pg        = pg_ics_tc, 
  nombre_serie = "ICS", 
  col_tva      = "tva_ics", 
  df_difusion  = df_di_ics_intermensual
)

tabla_eval_ica <- evaluar_puntos_giro_3d(
  df_datos     = df_eval_tva, 
  df_pg        = pg_ica_tc, 
  nombre_serie = "ICA (4.2)", 
  col_tva      = "tva_ica", 
  df_difusion  = df_di_ica_intermensual_4
)

tabla_3d_completa <- bind_rows(tabla_eval_ics, tabla_eval_ica)

cat("\n==================================================================\n")
cat(" AUDITORÍA DE PROFUNDIDAD Y DIFUSIÓN DE PUNTOS DE GIRO (REGLA 3 D)\n")
cat("==================================================================\n")
print(knitr::kable(tabla_3d_completa, align = "c"))

# ==============================================================================
# COMPARACIÓN DE SINCRONÍA CÍCLICA: INDICADORES LÍDERES INDIVIDUALES VS. ICS
# Transformaciones:
# 1. Estandarización directa sobre Tendencia-Ciclo Pura (Puntajes Z)
# 2. Log-HP (λ = 14.400) -> Estandarización (Puntajes Z)
# ==============================================================================

color_ics <- "#003366"          
color_lider <- "#B7950B"        

df_sincronia <- df_series_mensual %>%
  select(fecha, indice_coincidente, ics_tc) %>% 
  inner_join(df_ica_series %>% select(fecha, auto_tc, moto_tc, escrituras_tc, cemento_tc), by = "fecha") %>%
  drop_na()

aplicar_log_hp <- function(serie, lambda = 14400) {
  ts_obj <- ts(log(serie), start = c(year(min(df_sincronia$fecha)), month(min(df_sincronia$fecha))), frequency = 12)
  hp_res <- hpfilter(ts_obj, freq = lambda, type = "lambda")
  return(as.numeric(hp_res$trend))
}

df_sincronia_z <- df_sincronia %>%
  mutate(
    ics_tc_z        = as.numeric(scale(ics_tc)),
    auto_tc_z       = as.numeric(scale(auto_tc)),
    moto_tc_z       = as.numeric(scale(moto_tc)),
    escrituras_tc_z = as.numeric(scale(escrituras_tc)),
    cemento_tc_z    = as.numeric(scale(cemento_tc)),
    
    ics_log_hp        = aplicar_log_hp(indice_coincidente),
    auto_log_hp       = aplicar_log_hp(auto_tc),
    moto_log_hp       = aplicar_log_hp(moto_tc),
    escrituras_log_hp = aplicar_log_hp(escrituras_tc),
    cemento_log_hp    = aplicar_log_hp(cemento_tc),
    
    ics_hp_z        = as.numeric(scale(ics_log_hp)),
    auto_hp_z       = as.numeric(scale(auto_log_hp)),
    moto_hp_z       = as.numeric(scale(moto_log_hp)),
    escrituras_hp_z = as.numeric(scale(escrituras_log_hp)),
    cemento_hp_z    = as.numeric(scale(cemento_log_hp))
  )

# ==============================================================================
# SECCIÓN A: GRÁFICOS SOBRE SERIE TENDENCIA-CICLO (TC) PURA ESTANDARIZADA
# ==============================================================================

# ------------------------------------------------------------------------------
# GRÁFICO A.1: COMERCIO AUTOMOTOR (TC PURA) VS. ICS
# ------------------------------------------------------------------------------
plot_sync_auto_tc <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  geom_line(aes(y = auto_tc_z, color = "Comercio Automotor (Líder)"), linewidth = 1.1) +
  geom_line(aes(y = ics_tc_z, color = "ICS (Referencia)"), linewidth = 1.2) +
  scale_color_manual(
    name = "Series",
    values = c("ICS (Referencia)" = color_ics, "Comercio Automotor (Líder)" = color_lider)
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_sync_auto_tc)

# ------------------------------------------------------------------------------
# GRÁFICO A.2: MOTOVEHÍCULOS (TC PURA) VS. ICS
# ------------------------------------------------------------------------------
plot_sync_moto_tc <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  geom_line(aes(y = moto_tc_z, color = "Motovehículos (Líder)"), linewidth = 1.1) +
  geom_line(aes(y = ics_tc_z, color = "ICS (Referencia)"), linewidth = 1.2) +
  scale_color_manual(
    name = "Series",
    values = c("ICS (Referencia)" = color_ics, "Motovehículos (Líder)" = color_lider)
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_sync_moto_tc)

# ------------------------------------------------------------------------------
# GRÁFICO A.3: ESCRITURAS DE COMPRAVENTA (TC PURA) VS. ICS
# ------------------------------------------------------------------------------
plot_sync_escrituras_tc <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  geom_line(aes(y = escrituras_tc_z, color = "Escrituras de Compraventa (Líder)"), linewidth = 1.1) +
  geom_line(aes(y = ics_tc_z, color = "ICS (Referencia)"), linewidth = 1.2) +
  scale_color_manual(
    name = "Series",
    values = c("ICS (Referencia)" = color_ics, "Escrituras de Compraventa (Líder)" = color_lider)
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_sync_escrituras_tc)

# ------------------------------------------------------------------------------
# GRÁFICO A.4: DESPACHOS DE CEMENTO (TC PURA) VS. ICS
# ------------------------------------------------------------------------------
plot_sync_cemento_tc <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  geom_line(aes(y = cemento_tc_z, color = "Despachos de Cemento (Líder)"), linewidth = 1.1) +
  geom_line(aes(y = ics_tc_z, color = "ICS (Referencia)"), linewidth = 1.2) +
  scale_color_manual(
    name = "Series",
    values = c("ICS (Referencia)" = color_ics, "Despachos de Cemento (Líder)" = color_lider)
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_sync_cemento_tc)


# ==============================================================================
# SECCIÓN B: GRÁFICOS SOBRE SERIE FILTRADA (LOG-HP) ESTANDARIZADA
# ==============================================================================

# ------------------------------------------------------------------------------
# GRÁFICO B.1: COMERCIO AUTOMOTOR (LOG-HP) VS. ICS
# ------------------------------------------------------------------------------
plot_sync_auto_hp <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  geom_line(aes(y = auto_hp_z, color = "Comercio Automotor (Líder)"), linewidth = 1.1) +
  geom_line(aes(y = ics_hp_z, color = "ICS (Referencia)"), linewidth = 1.2) +
  scale_color_manual(
    name = "Series",
    values = c("ICS (Referencia)" = color_ics, "Comercio Automotor (Líder)" = color_lider)
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_sync_auto_hp)

# ------------------------------------------------------------------------------
# GRÁFICO B.2: MOTOVEHÍCULOS (LOG-HP) VS. ICS
# ------------------------------------------------------------------------------
plot_sync_moto_hp <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  geom_line(aes(y = moto_hp_z, color = "Motovehículos (Líder)"), linewidth = 1.1) +
  geom_line(aes(y = ics_hp_z, color = "ICS (Referencia)"), linewidth = 1.2) +
  scale_color_manual(
    name = "Series",
    values = c("ICS (Referencia)" = color_ics, "Motovehículos (Líder)" = color_lider)
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_sync_moto_hp)

# ------------------------------------------------------------------------------
# GRÁFICO B.3: ESCRITURAS DE COMPRAVENTA (LOG-HP) VS. ICS
# ------------------------------------------------------------------------------
plot_sync_escrituras_hp <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  geom_line(aes(y = escrituras_hp_z, color = "Escrituras de Compraventa (Líder)"), linewidth = 1.1) +
  geom_line(aes(y = ics_hp_z, color = "ICS (Referencia)"), linewidth = 1.2) +
  scale_color_manual(
    name = "Series",
    values = c("ICS (Referencia)" = color_ics, "Escrituras de Compraventa (Líder)" = color_lider)
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_sync_escrituras_hp)

# ------------------------------------------------------------------------------
# GRÁFICO B.4: DESPACHOS DE CEMENTO (LOG-HP) VS. ICS
# ------------------------------------------------------------------------------
plot_sync_cemento_hp <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  geom_line(aes(y = cemento_hp_z, color = "Despachos de Cemento (Líder)"), linewidth = 1.1) +
  geom_line(aes(y = ics_hp_z, color = "ICS (Referencia)"), linewidth = 1.2) +
  scale_color_manual(
    name = "Series",
    values = c("ICS (Referencia)" = color_ics, "Despachos de Cemento (Líder)" = color_lider)
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  )

print(plot_sync_cemento_hp)

# ------------------------------------------------------------------------------
# GRÁFICO B.5: TODOS LOS COMPONENTES (ICA 4.2 HP) VS. ICS EN CONJUNTO
# ------------------------------------------------------------------------------
colores_calidos_hp <- c(
  "ICS (Referencia)"          = "#003366", 
  "Comercio Automotor"        = "#C0392B", 
  "Motovehículos"             = "#D35400", 
  "Escrituras de Compraventa" = "#F39C12", 
  "Despachos de Cemento"      = "#E74C3C"  
)

plot_sync_todas_hp <- ggplot(data = df_sincronia_z, aes(x = fecha)) +
  geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
  
  geom_line(aes(y = auto_hp_z, color = "Comercio Automotor"), linewidth = 0.9, alpha = 0.85) +
  geom_line(aes(y = moto_hp_z, color = "Motovehículos"), linewidth = 0.9, alpha = 0.85) +
  geom_line(aes(y = escrituras_hp_z, color = "Escrituras de Compraventa"), linewidth = 0.9, alpha = 0.85) +
  geom_line(aes(y = cemento_hp_z, color = "Despachos de Cemento"), linewidth = 0.9, alpha = 0.85) +
  
  geom_line(aes(y = ics_hp_z, color = "ICS (Referencia)"), linewidth = 1.4) +
  
  scale_color_manual(
    name = "Series",
    values = colores_calidos_hp,
    breaks = c("ICS (Referencia)", "Comercio Automotor", "Motovehículos", "Escrituras de Compraventa", "Despachos de Cemento")
  ) +
  scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_sincronia_z$fecha, na.rm = TRUE), max(df_sincronia_z$fecha, na.rm = TRUE)), expand = c(0, 0)) +
  coord_cartesian(clip = "off") +
  labs(
    title = NULL,
    subtitle = NULL,
    x = NULL,
    y = "Desviaciones Estándar (Z)"
  ) +
  theme_minimal(base_size = 11, base_family = "sans") +
  theme(
    plot.title = element_text(face = "bold", hjust = 0.5),
    plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)),
    legend.position = "bottom",
    legend.title = element_text(face = "bold"),
    panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
    plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
  ) +
  guides(color = guide_legend(nrow = 2, byrow = TRUE))

print(plot_sync_todas_hp)

# ==============================================================================
# TEST DE CORRELACIÓN CRUZADA (CCF) Y CAUSALIDAD DE GRANGER COMPARATIVOS
# Comparación: 4 Variables Líderes Individuales vs. ICA 4.2 contra el ICS
# ==============================================================================

df_ccf <- df_series_mensual %>%
  select(fecha, ics_tc) %>%
  inner_join(
    df_ica_series %>% select(fecha, auto_tc, moto_tc, escrituras_tc, cemento_tc, ica_tc), 
    by = "fecha"
  ) %>%
  drop_na()

calc_sym_rate <- function(x) {
  200 * (x - dplyr::lag(x, 1)) / (x + dplyr::lag(x, 1))
}

df_tasas <- df_ccf %>%
  mutate(
    ics_sym        = calc_sym_rate(ics_tc),
    auto_sym       = calc_sym_rate(auto_tc),
    moto_sym       = calc_sym_rate(moto_tc),
    escrituras_sym = calc_sym_rate(escrituras_tc),
    cemento_sym    = calc_sym_rate(cemento_tc),
    ica_sym        = calc_sym_rate(ica_tc)
  ) %>%
  drop_na()

# ------------------------------------------------------------------------------
# A. TABLA COMPARATIVA DE CORRELACIÓN CRUZADA (CCF)
# ------------------------------------------------------------------------------
analizar_ccf_lags <- function(nombre_var, serie_lider, serie_ref) {
  res_ccf <- ccf(serie_lider, serie_ref, lag.max = 12, plot = FALSE)
  
  extraer_cor <- function(l) {
    idx <- which(res_ccf$lag[, 1, 1] == l)
    round(res_ccf$acf[idx, 1, 1], 3)
  }
  
  cor_t_minus6 <- extraer_cor(-6)
  cor_t_minus3 <- extraer_cor(-3)
  cor_t_minus1 <- extraer_cor(-1)
  cor_t_0      <- extraer_cor(0)
  cor_t_plus1  <- extraer_cor(1)
  cor_t_plus3  <- extraer_cor(3)
  cor_t_plus6  <- extraer_cor(6)
  
  idx_max <- which.max(abs(res_ccf$acf[, 1, 1]))
  max_lag <- res_ccf$lag[idx_max, 1, 1]
  max_cor <- res_ccf$acf[idx_max, 1, 1]
  
  t_max_str <- sprintf("t%+d (r = %.3f)", max_lag, max_cor)
  if(max_lag == 0) t_max_str <- sprintf("t0 (r = %.3f)", max_cor)
  
  return(data.frame(
    Variable = nombre_var,
    `t-6` = cor_t_minus6,
    `t-3` = cor_t_minus3,
    `t-1` = cor_t_minus1,
    `t0`  = cor_t_0,
    `t+1` = cor_t_plus1,
    `t+3` = cor_t_plus3,
    `t+6` = cor_t_plus6,
    `Max_Periodo` = t_max_str,
    check.names = FALSE
  ))
}

tabla_auto    <- analizar_ccf_lags("Comercio Automotor", df_tasas$auto_sym, df_tasas$ics_sym)
tabla_moto    <- analizar_ccf_lags("Motovehículos", df_tasas$moto_sym, df_tasas$ics_sym)
tabla_esc     <- analizar_ccf_lags("Escrituras de Compraventa", df_tasas$escrituras_sym, df_tasas$ics_sym)
tabla_cemento <- analizar_ccf_lags("Despachos de Cemento", df_tasas$cemento_sym, df_tasas$ics_sym)
tabla_ica     <- analizar_ccf_lags("ICA 4.2 (4 Componentes)", df_tasas$ica_sym, df_tasas$ics_sym)

tabla_ccf_final <- bind_rows(tabla_auto, tabla_moto, tabla_esc, tabla_cemento, tabla_ica)

cat("\n========================================================================================\n")
cat(" TABLA: CORRELACIÓN CRUZADA (CCF) - COMPONENTES INDIVIDUALES Y ICA 4.2 VS. ICS\n")
cat(" Nota: Valores 't' negativos indican que la variable ADELANTA al ICS.\n")
cat("========================================================================================\n\n")

print(knitr::kable(tabla_ccf_final, align = "c"))

# ------------------------------------------------------------------------------
# B. TABLA COMPARATIVA DE CAUSALIDAD DE GRANGER EN SERIES DESESTACIONALIZADAS (X -> ICS)
# ------------------------------------------------------------------------------

df_tasas_sa <- df_series_mensual %>%
  select(fecha, ics_sa = indice_coincidente) %>%
  inner_join(
    df_ica_series %>%
      mutate(
        auto_sa_val       = if("auto_sa" %in% names(.)) auto_sa else df_auto_limpio$sa_obj_ts[match(fecha, df_auto_limpio$fecha)],
        moto_sa_val       = if("moto_sa" %in% names(.)) moto_sa else df_moto_limpio$sa_obj_ts[match(fecha, df_moto_limpio$fecha)],
        escrituras_sa_val = if("escrituras_sa" %in% names(.)) escrituras_sa else df_escrituras_limpio$sa_obj_ts[match(fecha, df_escrituras_limpio$fecha)],
        cemento_sa_val    = if("cemento_sa" %in% names(.)) cemento_sa else df_cemento_completo$sa_obj_ts[match(fecha, df_cemento_completo$fecha)]
      ) %>%
      select(fecha, auto_sa_val, moto_sa_val, escrituras_sa_val, cemento_sa_val),
    by = "fecha"
  ) %>%
  arrange(fecha) %>%
  mutate(
    ics_sym_sa        = calc_variacion_simetrica(ics_sa),
    auto_sym_sa       = calc_variacion_simetrica(auto_sa_val),
    moto_sym_sa       = calc_variacion_simetrica(moto_sa_val),
    escrituras_sym_sa = calc_variacion_simetrica(escrituras_sa_val),
    cemento_sym_sa    = calc_variacion_simetrica(cemento_sa_val),
    
    ica_sym_sa        = as.numeric(unname(weights_ica["auto_sym"]))       * auto_sym_sa +
      as.numeric(unname(weights_ica["moto_sym"]))       * moto_sym_sa +
      as.numeric(unname(weights_ica["escrituras_sym"])) * escrituras_sym_sa +
      as.numeric(unname(weights_ica["cemento_sym"]))    * cemento_sym_sa
  ) %>%
  drop_na()

analizar_granger_lags_sa <- function(nombre_var, serie_lider, serie_ref) {
  df_temp <- data.frame(r_ics = serie_ref, r_var = serie_lider)
  
  lags_eval <- c(1, 2, 3, 6, 12)
  
  stats_eval <- lapply(lags_eval, function(p) {
    g_test <- lmtest::grangertest(r_ics ~ r_var, order = p, data = df_temp)
    return(c(f_stat = g_test$F[2], p_val = g_test$`Pr(>F)`[2]))
  })
  
  all_tests <- lapply(1:12, function(p) {
    g_test <- lmtest::grangertest(r_ics ~ r_var, order = p, data = df_temp)
    return(c(f_stat = g_test$F[2], p_val = g_test$`Pr(>F)`[2]))
  })
  
  all_p_vals <- sapply(all_tests, function(x) x["p_val"])
  best_lag   <- which.min(all_p_vals)
  best_f     <- all_tests[[best_lag]]["f_stat"]
  best_p     <- all_p_vals[best_lag]
  
  data.frame(
    Variable               = nombre_var,
    `Lag 1 (F)`            = round(stats_eval[[1]]["f_stat"], 3),
    `Lag 1 (p-val)`        = round(stats_eval[[1]]["p_val"], 4),
    `Lag 2 (F)`            = round(stats_eval[[2]]["f_stat"], 3),
    `Lag 2 (p-val)`        = round(stats_eval[[2]]["p_val"], 4),
    `Lag 3 (F)`            = round(stats_eval[[3]]["f_stat"], 3),
    `Lag 3 (p-val)`        = round(stats_eval[[3]]["p_val"], 4),
    `Lag 6 (F)`            = round(stats_eval[[4]]["f_stat"], 3),
    `Lag 6 (p-val)`        = round(stats_eval[[4]]["p_val"], 4),
    `Lag 12 (F)`           = round(stats_eval[[5]]["f_stat"], 3),
    `Lag 12 (p-val)`       = round(stats_eval[[5]]["p_val"], 4),
    `Lag Óptimo`           = sprintf("Lag %d (F = %.3f, p = %.4f)", best_lag, best_f, best_p),
    `Causa a ICS (p<0.05)` = ifelse(best_p < 0.05, "SÍ (p < 0.05)", "NO"),
    check.names            = FALSE
  )
}

granger_auto    <- analizar_granger_lags_sa("Comercio Automotor", df_tasas_sa$auto_sym_sa, df_tasas_sa$ics_sym_sa)
granger_moto    <- analizar_granger_lags_sa("Motovehículos", df_tasas_sa$moto_sym_sa, df_tasas_sa$ics_sym_sa)
granger_esc     <- analizar_granger_lags_sa("Escrituras de Compraventa", df_tasas_sa$escrituras_sym_sa, df_tasas_sa$ics_sym_sa)
granger_cemento <- analizar_granger_lags_sa("Despachos de Cemento", df_tasas_sa$cemento_sym_sa, df_tasas_sa$ics_sym_sa)
granger_ica     <- analizar_granger_lags_sa("ICA 4.2 (4 Componentes)", df_tasas_sa$ica_sym_sa, df_tasas_sa$ics_sym_sa)

tabla_granger_comparativa <- bind_rows(granger_auto, granger_moto, granger_esc, granger_cemento, granger_ica)

cat("\n========================================================================================\n")
cat(" TABLA: TEST DE CAUSALIDAD DE GRANGER COMPARATIVO EN SERIES DESESTACIONALIZADAS (SA)\n")
cat(" (COMPONENTES INDIVIDUALES Y ICA 4.2 -> ICS)\n")
cat(" Nota: Valores F elevados y p-valores < 0.05 indican mayor capacidad predictiva sobre el ICS.\n")
cat("========================================================================================\n\n")

print(knitr::kable(tabla_granger_comparativa, align = "c"))

# ------------------------------------------------------------------------------
# TASAS DE VARIACIÓN DE LAS SERIES DESESTACIONALIZADAS (SA)
# ------------------------------------------------------------------------------

df_ica_sa_prep <- df_ica_series %>%
  mutate(
    auto_sa_val       = if("auto_sa" %in% names(.)) auto_sa else df_auto_limpio$sa_obj_ts[match(fecha, df_auto_limpio$fecha)],
    moto_sa_val       = if("moto_sa" %in% names(.)) moto_sa else df_moto_limpio$sa_obj_ts[match(fecha, df_moto_limpio$fecha)],
    escrituras_sa_val = if("escrituras_sa" %in% names(.)) escrituras_sa else df_escrituras_limpio$sa_obj_ts[match(fecha, df_escrituras_limpio$fecha)],
    cemento_sa_val    = if("cemento_sa" %in% names(.)) cemento_sa else df_cemento_completo$sa_obj_ts[match(fecha, df_cemento_completo$fecha)],
    
    auto_sym_sa       = calc_variacion_simetrica(auto_sa_val),
    moto_sym_sa       = calc_variacion_simetrica(moto_sa_val),
    escrituras_sym_sa = calc_variacion_simetrica(escrituras_sa_val),
    cemento_sym_sa    = calc_variacion_simetrica(cemento_sa_val),
    
    r_ica_sa = as.numeric(unname(weights_ica["auto_sym"]))       * auto_sym_sa +
      as.numeric(unname(weights_ica["moto_sym"]))       * moto_sym_sa +
      as.numeric(unname(weights_ica["escrituras_sym"])) * escrituras_sym_sa +
      as.numeric(unname(weights_ica["cemento_sym"]))    * cemento_sym_sa
  ) %>%
  select(fecha, r_ica_sa)

df_eval_global_sa <- df_series_mensual %>%
  select(fecha, ics_sa = indice_coincidente) %>%
  inner_join(df_ica_sa_prep, by = "fecha") %>%
  arrange(fecha) %>%
  mutate(
    r_ics_sa = 200 * (ics_sa - lag(ics_sa)) / (ics_sa + lag(ics_sa))
  ) %>%
  filter(!is.na(r_ics_sa) & !is.na(r_ica_sa))

# ------------------------------------------------------------------------------
# EJECUCIÓN DEL TEST DE CAUSALIDAD DE GRANGER EN PRIMERAS DIFERENCIAS (SA)
# Evaluado de Lag 1 a Lag 12 meses
# ------------------------------------------------------------------------------

res_granger_sa_lags <- purrr::map_dfr(1:12, function(p) {
  # Test Directo: ¿El ICA en SA Granger-causa al ICS en SA?
  g_fwd <- lmtest::grangertest(r_ics_sa ~ r_ica_sa, order = p, data = df_eval_global_sa)
  
  # Test Inverso: ¿El ICS en SA Granger-causa al ICA en SA?
  g_rev <- lmtest::grangertest(r_ica_sa ~ r_ics_sa, order = p, data = df_eval_global_sa)
  
  data.frame(
    `Lag (Meses)`            = p,
    `F (ICA -> ICS)`         = round(g_fwd$F[2], 3),
    `p-val (ICA -> ICS)`     = round(g_fwd$`Pr(>F)`[2], 4),
    `Significativo (Directo)`= ifelse(g_fwd$`Pr(>F)`[2] < 0.05, "SÍ (p < 0.05)", "NO"),
    `F (ICS -> ICA)`         = round(g_rev$F[2], 3),
    `p-val (ICS -> ICA)`     = round(g_rev$`Pr(>F)`[2], 4),
    `Causalidad Inversa`     = ifelse(g_rev$`Pr(>F)`[2] < 0.05, "DETECTADA", "NO (Exógeno)"),
    check.names              = FALSE
  )
})

# ------------------------------------------------------------------------------
# 3. IMPRESIÓN DE LA TABLA DE RESULTADOS EN CONSOLA
# ------------------------------------------------------------------------------

cat("\n========================================================================================\n")
cat(" TEST DE CAUSALIDAD DE GRANGER SOBRE SERIES DESESTACIONALIZADAS (SA) (ICA 4.2 VS ICS)\n")
cat(" Metodología: Primera diferencia de series desestacionalizadas (Galaso & Rodríguez López, 2014)\n")
cat("========================================================================================\n\n")

print(knitr::kable(res_granger_sa_lags, align = "c", caption = "Tabla 4.7. Test de Causalidad de Granger en Series Desestacionalizadas (SA)"))

# ==============================================================================
# 7.3 EXÁMENES INDIVIDUALES DE COMPONENTES (ICA 4.2)
# Auditoría de Fases, Ciclos y Gráficos Comparativos de Puntos de Giro vs ICS
# ==============================================================================

# ------------------------------------------------------------------------------
# 1. DETECCIÓN DE PUNTOS DE GIRO (BRY-BOSCHAN) POR COMPONENTE
# ------------------------------------------------------------------------------
pg_cemento    <- bry_boschan_nber(df_cemento_completo %>% filter(!is.na(cemento_tc)), col_y = "cemento_tc")
pg_auto       <- bry_boschan_nber(df_auto_limpio %>% filter(!is.na(auto_tc)), col_y = "auto_tc")
pg_moto       <- bry_boschan_nber(df_moto_limpio %>% filter(!is.na(moto_tc)), col_y = "moto_tc")
pg_escrituras <- bry_boschan_nber(df_escrituras_limpio %>% filter(!is.na(escrituras_tc)), col_y = "escrituras_tc")

# ------------------------------------------------------------------------------
# 2. TABLAS DE AUDITORÍA (DURACIÓN DE FASES Y CICLOS)
# ------------------------------------------------------------------------------
audit_cemento    <- auditar_tiempos_bb(pg_cemento, df_cemento_completo)
audit_auto       <- auditar_tiempos_bb(pg_auto, df_auto_limpio)
audit_moto       <- auditar_tiempos_bb(pg_moto, df_moto_limpio)
audit_escrituras <- auditar_tiempos_bb(pg_escrituras, df_escrituras_limpio)

# ------------------------------------------------------------------------------
# 3. FUNCIÓN PARA GRAFICAR SINCRONÍA DE PUNTOS DE GIRO (TC ESTANDARIZADA)
# ------------------------------------------------------------------------------
graficar_sync_bb <- function(df_z, col_lider_z, pg_lider, pg_ics, titulo_lider, col_lider_hex = "#B7950B") {
  
  df_lineas <- df_z %>% select(fecha, ics_tc_z, lider_z = all_of(col_lider_z))
  
  pg_lider_z <- pg_lider %>% 
    inner_join(df_lineas, by = "fecha") %>% 
    mutate(Etiqueta = paste0(ifelse(Tipo == "Peak", "Pico", "Valle"), " (Líder)")) %>%
    select(fecha, Valor = lider_z, Etiqueta)
  
  pg_ics_z <- pg_ics %>% 
    inner_join(df_lineas, by = "fecha") %>% 
    mutate(Etiqueta = paste0(ifelse(Tipo == "Peak", "Pico", "Valle"), " (ICS)")) %>%
    select(fecha, Valor = ics_tc_z, Etiqueta)
  
  df_pg_comb <- bind_rows(pg_ics_z, pg_lider_z)
  
  p <- ggplot(data = df_lineas, aes(x = fecha)) +
    geom_hline(yintercept = 0, linetype = "dashed", color = "grey50", linewidth = 0.8) +
    
    
    geom_line(aes(y = lider_z, color = "Líder (TC)"), linewidth = 1.1) +
    geom_line(aes(y = ics_tc_z, color = "ICS (TC)"), linewidth = 1.2) +
    
    {if(nrow(df_pg_comb) > 0) geom_point(data = df_pg_comb, aes(y = Valor, color = Etiqueta, shape = Etiqueta), size = 3.5)} +
    
    scale_color_manual(
      name = "Referencias",
      values = c(
        "ICS (TC)" = "#003366", "Líder (TC)" = col_lider_hex,
        "Pico (ICS)" = "#0066CC", "Valle (ICS)" = "#000033",
        "Pico (Líder)" = "#FF3300", "Valle (Líder)" = "#228B22"
      ),
      breaks = c("ICS (TC)", "Líder (TC)", "Pico (ICS)", "Valle (ICS)", "Pico (Líder)", "Valle (Líder)")
    ) +
    scale_shape_manual(
      name = "Referencias",
      values = c(
        "ICS (TC)" = NA, "Líder (TC)" = NA,
        "Pico (ICS)" = 17, "Valle (ICS)" = 25,
        "Pico (Líder)" = 17, "Valle (Líder)" = 25
      ),
      breaks = c("ICS (TC)", "Líder (TC)", "Pico (ICS)", "Valle (ICS)", "Pico (Líder)", "Valle (Líder)")
    ) +
    scale_x_date(date_breaks = "2 years", date_labels = "%Y", limits = c(min(df_lineas$fecha, na.rm = TRUE), max(df_lineas$fecha, na.rm = TRUE)), expand = c(0, 0)) +
    coord_cartesian(clip = "off") +
    labs(
      title = NULL,
      subtitle = NULL,
      x = NULL, y = "Desviaciones Estándar (Z)"
    ) +
    theme_minimal(base_size = 11, base_family = "sans") +
    theme(
      plot.title = element_text(face = "bold", hjust = 0.5), 
      plot.subtitle = element_text(hjust = 0.5, color = "grey30", margin = margin(b = 10)), 
      legend.position = "bottom",
      panel.border = element_rect(color = "black", fill = NA, linewidth = 0.5), axis.ticks = element_line(color = "black", linewidth = 0.5), axis.ticks.length = unit(0.15, "cm"),
      plot.margin = margin(t = 10, r = 15, b = 10, l = 15)
    ) +
    guides(
      color = guide_legend(
        nrow = 2, byrow = TRUE,
        override.aes = list(
          linetype = c("solid", "solid", "blank", "blank", "blank", "blank"), 
          shape = c(NA, NA, 17, 25, 17, 25)
        )
      ), 
      shape = "none"
    )
  
  return(p)
}

# ------------------------------------------------------------------------------
# 4. IMPRESIÓN DE RESULTADOS POR COMPONENTE
# ------------------------------------------------------------------------------

# --- 4.1 DESPACHOS DE CEMENTO ---
cat("\n================================================================================================\n")
cat(" 1. DESPACHOS DE CEMENTO: AUDITORÍA DE CICLOS Y PUNTOS DE GIRO VS ICS\n")
cat("================================================================================================\n")
print(knitr::kable(audit_cemento, align = "c"))
plot_bb_cemento <- graficar_sync_bb(df_sincronia_z, "cemento_tc_z", pg_cemento, pg_ics_tc, "Despachos de Cemento", "#E74C3C")
print(plot_bb_cemento)

# --- 4.2 COMERCIO AUTOMOTOR ---
cat("\n================================================================================================\n")
cat(" 2. COMERCIO AUTOMOTOR: AUDITORÍA DE CICLOS Y PUNTOS DE GIRO VS ICS\n")
cat("================================================================================================\n")
print(knitr::kable(audit_auto, align = "c"))
plot_bb_auto <- graficar_sync_bb(df_sincronia_z, "auto_tc_z", pg_auto, pg_ics_tc, "Comercio Automotor", "#C0392B")
print(plot_bb_auto)

# --- 4.3 MOTOVEHÍCULOS ---
cat("\n================================================================================================\n")
cat(" 3. MOTOVEHÍCULOS: AUDITORÍA DE CICLOS Y PUNTOS DE GIRO VS ICS\n")
cat("================================================================================================\n")
print(knitr::kable(audit_moto, align = "c"))
plot_bb_moto <- graficar_sync_bb(df_sincronia_z, "moto_tc_z", pg_moto, pg_ics_tc, "Motovehículos", "#D35400")
print(plot_bb_moto)

# --- 4.4 ESCRITURAS DE COMPRAVENTA ---
cat("\n================================================================================================\n")
cat(" 4. ESCRITURAS DE COMPRAVENTA: AUDITORÍA DE CICLOS Y PUNTOS DE GIRO VS ICS\n")
cat("================================================================================================\n")
print(knitr::kable(audit_escrituras, align = "c"))
plot_bb_escrituras <- graficar_sync_bb(df_sincronia_z, "escrituras_tc_z", pg_escrituras, pg_ics_tc, "Escrituras Inmobiliarias", "#F39C12")
print(plot_bb_escrituras)

# ------------------------------------------------------------------------------
# B. TABLAS EXTENDIDAS DE CAUSALIDAD DE GRANGER (Rezagos 1 a 12)
# H0: Lider NO causa a ICS  |  H0: ICS NO causa a Lider
# ------------------------------------------------------------------------------

# Función para generar la tabla extendida de Granger para una variable específica
analizar_granger_extendido <- function(nombre_var, serie_lider, serie_ref, lags = 1:12) {
  df_temp <- data.frame(r_ics = serie_ref, r_var = serie_lider)
  
  resultados <- lapply(lags, function(p) {
    # Test Dirección 1: Lider -> ICS (¿La variable líder ayuda a predecir el ICS?)
    g_test_1 <- lmtest::grangertest(r_ics ~ r_var, order = p, data = df_temp)
    f_stat_1 <- g_test_1$F[2]
    p_val_1  <- g_test_1$`Pr(>F)`[2]
    
    # Test Dirección 2: ICS -> Lider (¿El ICS ayuda a predecir la variable líder? - Prueba de bidireccionalidad)
    g_test_2 <- lmtest::grangertest(r_var ~ r_ics, order = p, data = df_temp)
    f_stat_2 <- g_test_2$F[2]
    p_val_2  <- g_test_2$`Pr(>F)`[2]
    
    data.frame(
      Variable = nombre_var,
      Rezago = p,
      `F (Líder -> ICS)` = round(f_stat_1, 3),
      `p-valor (Líder -> ICS)` = round(p_val_1, 4),
      `Significativo L->ICS` = ifelse(p_val_1 < 0.05, "*", ""),
      `F (ICS -> Líder)` = round(f_stat_2, 3),
      `p-valor (ICS -> Líder)` = round(p_val_2, 4),
      `Significativo ICS->L` = ifelse(p_val_2 < 0.05, "*", ""),
      check.names = FALSE
    )
  })
  
  return(bind_rows(resultados))
}

granger_ext_auto    <- analizar_granger_extendido("Comercio Automotor", df_tasas$auto_sym, df_tasas$ics_sym)
granger_ext_moto    <- analizar_granger_extendido("Motovehículos", df_tasas$moto_sym, df_tasas$ics_sym)
granger_ext_esc     <- analizar_granger_extendido("Escrituras", df_tasas$escrituras_sym, df_tasas$ics_sym)
granger_ext_cemento <- analizar_granger_extendido("Despachos Cemento", df_tasas$cemento_sym, df_tasas$ics_sym)

tabla_granger_componentes <- bind_rows(granger_ext_auto, granger_ext_moto, granger_ext_esc, granger_ext_cemento)

tabla_granger_ica <- analizar_granger_extendido("ICA 4.2", df_tasas$ica_sym, df_tasas$ics_sym)

cat("\n========================================================================================\n")
cat(" TEST DE CAUSALIDAD DE GRANGER EXTENDIDO (Lags 1 a 12): COMPONENTES INDIVIDUALES VS. ICS\n")
cat(" H0 (Líder -> ICS): La variable adelantada NO causa en sentido Granger al ICS.\n")
cat(" H0 (ICS -> Líder): El ICS NO causa en sentido Granger a la variable adelantada.\n")
cat(" (*) Indica significancia estadística (p < 0.05) rechazando H0.\n")
cat("========================================================================================\n\n")
print(knitr::kable(tabla_granger_componentes, align = "c"))

cat("\n========================================================================================\n")
cat(" TEST DE CAUSALIDAD DE GRANGER EXTENDIDO (Lags 1 a 12): ÍNDICE COMPUESTO (ICA 4.2) VS. ICS\n")
cat(" H0 (Líder -> ICS): El ICA 4.2 NO causa en sentido Granger al ICS.\n")
cat(" H0 (ICS -> Líder): El ICS NO causa en sentido Granger al ICA 4.2.\n")
cat(" (*) Indica significancia estadística (p < 0.05) rechazando H0.\n")
cat("========================================================================================\n\n")
print(knitr::kable(tabla_granger_ica, align = "c"))