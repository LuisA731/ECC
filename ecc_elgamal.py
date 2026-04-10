import random
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches

INFINITO = None  


# ═══════════════════════════════════════════════════════════════
# 2.2  INVERSO MODULAR  (Algoritmo Extendido de Euclides)
# ═══════════════════════════════════════════════════════════════
def inverso_mod(k, p):
    """Calcula el inverso modular de k módulo p usando el algoritmo extendido de Euclides."""
    if k == 0:
        raise ValueError("No existe inverso de 0")

    if k < 0:
        return p - inverso_mod(-k, p)

    s_prev, s_act = 1, 0
    t_prev, t_act = 0, 1
    r_prev, r_act = k, p

    while r_act != 0:
        q = r_prev // r_act
        r_prev, r_act = r_act, r_prev - q * r_act
        s_prev, s_act = s_act, s_prev - q * s_act
        t_prev, t_act = t_act, t_prev - q * t_act

    if r_prev != 1:
        raise ValueError("k y p no son coprimos")

    return s_prev % p


# ═══════════════════════════════════════════════════════════════
# 2.3  VERIFICACIÓN DE PUNTO VÁLIDO
# ═══════════════════════════════════════════════════════════════
def es_punto_valido(P, a, b, p):
    """Verifica si el punto P pertenece a la curva elíptica."""
    if P is INFINITO:
        return True

    x, y = P
    return (y**2 - (x**3 + a*x + b)) % p == 0


# ═══════════════════════════════════════════════════════════════
# 2.4  NEGACIÓN DE UN PUNTO
# ═══════════════════════════════════════════════════════════════
def negar_punto(P, p):
    """Retorna el inverso aditivo de P: −P = (x, −y mod p)."""
    if P is INFINITO:
        return INFINITO

    x, y = P
    return (x, (-y) % p)


# ═══════════════════════════════════════════════════════════════
# 2.5  SUMA DE PUNTOS
# ═══════════════════════════════════════════════════════════════
def sumar_puntos(P, Q, a, p):
    """
    Suma dos puntos de la curva elíptica.
    Casos cubiertos:
      1. Punto neutro
      2. Puntos verticales (resultado = INFINITO)
      3. Suma de puntos distintos
      4. Doblado de punto (P == Q)
    """
    # Caso 1: Punto neutro
    if P is INFINITO:
        return Q
    if Q is INFINITO:
        return P

    x1, y1 = P
    x2, y2 = Q

    # Caso 2: Puntos verticales → resultado es el punto al infinito
    if x1 == x2 and (y1 + y2) % p == 0:
        return INFINITO

    # Caso 3 y 4: Calcular pendiente
    if P != Q:
        # Suma de puntos distintos
        m = ((y2 - y1) * inverso_mod(x2 - x1, p)) % p
    else:
        # Doblado de punto (P == Q)
        m = ((3 * x1**2 + a) * inverso_mod(2 * y1, p)) % p

    x3 = (m**2 - x1 - x2) % p
    y3 = (m * (x1 - x3) - y1) % p

    return (x3, y3)


# ═══════════════════════════════════════════════════════════════
# 2.6  MULTIPLICACIÓN ESCALAR  (Double-and-Add)
# ═══════════════════════════════════════════════════════════════
def multiplicar_escalar(k, P, a, p):
    """
    Calcula Q = k·P usando el algoritmo double-and-add.
    """
    if (k % p == 0) or (P is INFINITO):
        return INFINITO

    if k < 0:
        return multiplicar_escalar(-k, negar_punto(P, p), a, p)

    resultado = INFINITO
    sumando   = P

    while k > 0:
        if (k & 1) == 1:                               
            resultado = sumar_puntos(resultado, sumando, a, p)
        sumando = sumar_puntos(sumando, sumando, a, p)  # doblado
        k >>= 1                                         # siguiente bit

    return resultado


# ═══════════════════════════════════════════════════════════════
# 3.1  CÁLCULO DEL ORDEN DE UN PUNTO
# ═══════════════════════════════════════════════════════════════
def calcular_orden(P, a, p, limite=2000):
    """Calcula el orden del punto P iterando sumas hasta obtener INFINITO."""
    actual = INFINITO

    for n in range(1, limite + 1):
        actual = sumar_puntos(actual, P, a, p)
        if actual is INFINITO:
            return n

    return None   # No encontrado dentro del límite


# ═══════════════════════════════════════════════════════════════
# 3.2  BÚSQUEDA DE PUNTO GENERADOR
# ═══════════════════════════════════════════════════════════════
def buscar_punto_generador(a, b, p, orden_minimo=300):
    """
    Busca un punto G en la curva con orden > orden_minimo.
    Necesario para que el subgrupo sea suficientemente grande
    y se puedan mapear todos los caracteres ASCII sin colisiones.
    """
    for x in range(p):
        rhs = (x**3 + a*x + b) % p

        for y in range(p):
            if (y**2) % p == rhs:
                P = (x, y)
                orden = calcular_orden(P, a, p)

                if orden is not None and orden > orden_minimo:
                    return P, orden

    raise ValueError("No se encontró punto con orden suficiente")


# ═══════════════════════════════════════════════════════════════
# 3.3  TABLA ASCII ↔ PUNTO ECC
# ═══════════════════════════════════════════════════════════════
def construir_tabla_ascii(G, a, p, max_ascii=255):
    """
    Construye la correspondencia bidireccional:
      ASCII value  ←→  Punto ECC = m·G
    Permite cifrar y descifrar mensajes de texto arbitrarios.
    """
    ascii_a_punto = {}
    punto_a_ascii = {}

    for m in range(1, max_ascii + 1):
        P = multiplicar_escalar(m, G, a, p)
        ascii_a_punto[m] = P
        punto_a_ascii[P] = m

    return ascii_a_punto, punto_a_ascii


# ═══════════════════════════════════════════════════════════════
# 4.1  CIFRADO ElGamal sobre ECC
# ═══════════════════════════════════════════════════════════════
def cifrar_punto_ecc(M, k, G, clave_publica, a, p):
    """
    Cifra el punto mensaje M usando ElGamal sobre ECC.
    C1 = k·G          (punto efímero)
    S  = k·Q          (secreto compartido)
    C2 = M + S        (mensaje cifrado)
    Retorna: (C1, C2)
    """
    C1 = multiplicar_escalar(k, G, a, p)
    S  = multiplicar_escalar(k, clave_publica, a, p)
    C2 = sumar_puntos(M, S, a, p)

    return (C1, C2)


# ═══════════════════════════════════════════════════════════════
# 4.2  DESCIFRADO ElGamal sobre ECC
# ═══════════════════════════════════════════════════════════════
def descifrar_punto_ecc(C1, C2, clave_privada, a, p):
    """
    Descifra usando la clave privada d.
    S = d·C1 = d·k·G = k·Q    (se recupera el mismo secreto)
    M = C2 − S = C2 + (−S)
    """
    S = multiplicar_escalar(clave_privada, C1, a, p)
    M = sumar_puntos(C2, negar_punto(S, p), a, p)

    return M


# ═══════════════════════════════════════════════════════════════
# PUNTO EXTRA: GRÁFICA DE LA CURVA ELÍPTICA
# ═══════════════════════════════════════════════════════════════
def graficar_curva(a, b, p, G=None, Q=None, puntos_mensaje=None):
    """
    Genera DOS paneles lado a lado:
      Izquierda: curva continua sobre ℝ  (y² = x³+ax+b, forma clásica)
      Derecha  : puntos discretos sobre 𝔽_p  (lo que realmente usa ECC)
    """
    import os
    import numpy as np

    fig, (ax_r, ax_fp) = plt.subplots(1, 2, figsize=(16, 7))
    titulo = 'Curva eliptica: y2 = x3 + (a)x + b  |  Izquierda: sobre R (continua)     Derecha: sobre Fp (discreta ECC)'
    fig.suptitle(titulo, fontsize=12, fontweight='bold')

    # ── Panel izquierdo: curva CONTINUA sobre ℝ ─────────────
    # Rango amplio para capturar toda la forma de la curva
    x_vals = np.linspace(-4, 5, 4000)
    y2_vals = x_vals**3 + a * x_vals + b

    # Trazar rama superior e inferior (donde y²≥0)
    mask = y2_vals >= 0
    x_ok = x_vals[mask]
    y_pos = np.sqrt(y2_vals[mask])

    if len(x_ok) > 0:
        # Detectar discontinuidades (saltos >0.1 en x) para no unir ramas separadas
        gaps = np.where(np.diff(x_ok) > 0.15)[0]
        segments_x = np.split(x_ok, gaps + 1)
        segments_y = np.split(y_pos, gaps + 1)

        for sx, sy in zip(segments_x, segments_y):
            if len(sx) > 1:
                ax_r.plot(sx,  sy, color='#534AB7', linewidth=2.5)
                ax_r.plot(sx, -sy, color='#534AB7', linewidth=2.5)

    ax_r.axhline(0, color='gray', linewidth=0.6, linestyle='--', alpha=0.5)
    ax_r.axvline(0, color='gray', linewidth=0.6, linestyle='--', alpha=0.5)

    # Punto al infinito representado con una flecha hacia arriba
    ax_r.annotate('𝒪 (punto al infinito)', xy=(0, max(y_pos)*0.95 if len(y_pos)>0 else 5),
                  fontsize=9, ha='center', color='#534AB7',
                  arrowprops=dict(arrowstyle='->', color='#534AB7', lw=1),
                  xytext=(0, max(y_pos)*0.95 + 1.5 if len(y_pos)>0 else 6.5))

    ax_r.set_title('Sobre ℝ — curva continua', fontsize=11)
    ax_r.set_xlabel('x')
    ax_r.set_ylabel('y')
    ax_r.grid(True, alpha=0.25)
    # Ajustar ejes para que se vea la curva completa con margen
    if len(y_pos) > 0:
        ymax = max(y_pos) * 1.2
        ax_r.set_ylim(-ymax, ymax)
    ax_r.set_xlim(x_vals[0], x_vals[-1])

    # ── Panel derecho: puntos discretos sobre 𝔽_p ───────────
    xs, ys = [], []
    for x in range(p):
        rhs = (x**3 + a * x + b) % p
        for y in range(p):
            if (y * y) % p == rhs:
                xs.append(x)
                ys.append(y)

    ax_fp.scatter(xs, ys, s=1.5, color='#534AB7', alpha=0.5,
                  label=f'Puntos de la curva ({len(xs)})')

    if G is not None:
        ax_fp.scatter(*G, s=120, color='#1D9E75', zorder=6,
                      edgecolors='white', linewidths=0.8, label=f'Generador G={G}')
    if Q is not None:
        ax_fp.scatter(*Q, s=120, color='#E24B4A', zorder=6,
                      edgecolors='white', linewidths=0.8, label=f'Clave pública Q={Q}')
    if puntos_mensaje:
        px = [pt[0] for pt in puntos_mensaje if pt is not None]
        py = [pt[1] for pt in puntos_mensaje if pt is not None]
        ax_fp.scatter(px, py, s=80, color='#EF9F27', zorder=6,
                      edgecolors='white', linewidths=0.8, label='Puntos del mensaje')

    # Línea de simetría y = p/2
    ax_fp.axhline(p / 2, color='#E24B4A', linewidth=0.8, linestyle='--',
                  alpha=0.5, label=f'Simetría y = {p//2}')

    ax_fp.set_title(f'Sobre 𝔽_{p} — puntos discretos (ECC)', fontsize=11)
    ax_fp.set_xlabel('x  (mod p)')
    ax_fp.set_ylabel('y  (mod p)')
    ax_fp.legend(fontsize=8, markerscale=1.5)
    ax_fp.set_xlim(-10, p + 10)
    ax_fp.set_ylim(-10, p + 10)
    ax_fp.grid(True, alpha=0.12)

    plt.tight_layout()
    ruta = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'curva_eliptica.png')
    plt.savefig(ruta, dpi=150)
    plt.show()
    print(f"\n[GRÁFICA] Guardada en: {ruta}")






# ═══════════════════════════════════════════════════════════════
# PROGRAMA PRINCIPAL
# ═══════════════════════════════════════════════════════════════
def main():
    print("=" * 60)
    print("  EXAMEN PARCIAL 2 — Criptografía ECC + ElGamal")
    print("=" * 60)

    # ── 1. Parámetros de la curva  ────────
    p = 751
    a = -1
    b = 188

    interior         = 4 * a**3 + 27 * b**2
    discriminante_fp = (-16 * interior) % p

    print("\n[1] Parámetros de la curva elíptica  y² = x³ + ax + b (mod p)")
    print(f"    p = {p},  a = {a},  b = {b}")
    print(f"    Discriminante Δ = {discriminante_fp} (mod {p})  ≠ 0  ✓")
    # ── 2. Buscar punto generador G ──────────────────────────
    orden_minimo = 300   # fijo: suficiente para cubrir ASCII y mantener seguridad
    print(f"\n[2] Búsqueda de punto generador G (orden mínimo = {orden_minimo}) ...")

    try:
        G, orden_G = buscar_punto_generador(a, b, p, orden_minimo=orden_minimo)
    except ValueError as e:
        print(f"    ✗ {e}")
        print("    Intenta con parámetros de curva diferentes.")
        return

    print(f"    G = {G}")
    print(f"    Orden de G = {orden_G}")

    # ── 3. Generar claves ────────────────────────────────────
    semilla = 42   
    random.seed(semilla)
    print(f"\n[3] Generación de claves  (semilla fija = {semilla})")

    d_privada = random.randint(2, orden_G - 2)
    Q_publica = multiplicar_escalar(d_privada, G, a, p)

    print(f"\n    Clave privada  d = {d_privada}")
    print(f"    Clave pública  Q = d·G = {Q_publica}")


    # ── 4. Tabla ASCII ↔ ECC ─────────────────────────────────
    if orden_G <= 255:
        print("\n     El orden del generador no es suficiente para mapear ASCII sin colisiones.")
        return

    print("\n[4] Construyendo tabla ASCII ↔ Punto ECC ...")
    ascii_a_punto, punto_a_ascii = construir_tabla_ascii(G, a, p, max_ascii=255)
    print(f"    Tabla construida con {len(ascii_a_punto)} entradas.")

    # ── 5. Mensaje original ──────────────────────────────────
    print("\n[5] Mensaje a cifrar")
    while True:
        mensaje = input("    Ingresa el mensaje (solo caracteres ASCII 1-255): ")
        if not mensaje:
            print("     El mensaje no puede estar vacío.")
            continue
        codigos = [ord(c) for c in mensaje]
        invalidos = [c for c in codigos if c < 1 or c > 255]
        if invalidos:
            print(f"     Caracteres fuera de rango ASCII (1-255) detectados: {invalidos}")
            continue
        break

    ascii_mensaje = [ord(c) for c in mensaje]
    print(f"    Valores ASCII: {ascii_mensaje}")

    # ── 6. Convertir ASCII → Puntos ECC ─────────────────────
    puntos_mensaje = [ascii_a_punto[m] for m in ascii_mensaje]
    print(f"\n[6] Puntos ECC del mensaje:")
    for c, m, pt in zip(mensaje, ascii_mensaje, puntos_mensaje):
        print(f"    '{c}' (ASCII {m}) → {pt}")

    # ── 7. Cifrar cada punto con k efímero ───────────────────
    print("\n[7] Cifrando punto por punto (k efímero por carácter):")
    cifrado = []

    for i, M in enumerate(puntos_mensaje):
        k = random.randint(2, orden_G - 2)
        C1, C2 = cifrar_punto_ecc(M, k, G, Q_publica, a, p)
        cifrado.append((C1, C2))
        print(f"    '{mensaje[i]}' | k={k:4d} | C1={C1} | C2={C2}")

    # ── 8. Descifrar cada bloque ─────────────────────────────
    print("\n[8] Descifrando:")
    puntos_descifrados = []

    for i, (C1, C2) in enumerate(cifrado):
        M_recuperado = descifrar_punto_ecc(C1, C2, d_privada, a, p)
        puntos_descifrados.append(M_recuperado)
        ascii_val = punto_a_ascii.get(M_recuperado, None)
        char      = chr(ascii_val) if ascii_val else '?'
        print(f"    Bloque {i+1}: M recuperado = {M_recuperado}  → ASCII {ascii_val} → '{char}'")

    # ── 9. Reconstruir texto ─────────────────────────────────
    ascii_recuperado   = [punto_a_ascii[P] for P in puntos_descifrados]
    mensaje_recuperado = "".join(chr(n) for n in ascii_recuperado)

    print(f"\n[9] Mensaje recuperado: '{mensaje_recuperado}'")
    print(f"    Coincide con el original: {' SÍ' if mensaje_recuperado == mensaje else ' NO'}")


 
    # ── PUNTO EXTRA: Gráfica ──────────────────────────────────
    print("\n Generando gráfica de la curva elíptica ...")
    graficar_curva(a, b, p, G=G, Q=Q_publica, puntos_mensaje=puntos_mensaje)




# ─────────────────────────────────────────────
if __name__ == "__main__":
    main()