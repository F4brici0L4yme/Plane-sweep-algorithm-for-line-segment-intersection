import time
import math
import random
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

EPSILON = 1e-9
def subtract(p1, p2): return (p1[0] - p2[0], p1[1] - p2[1])
def cross_product(p1, p2, p3): return (p2[0] - p1[0]) * (p3[1] - p1[1]) - (p2[1] - p1[1]) * (p3[0] - p1[0])
def vector_cross_product(v1, v2): return v1[0] * v2[1] - v1[1] * v2[0]
def intersect_segments(p1, p2, q1, q2):
    v_p, v_q = subtract(p2, p1), subtract(q2, q1); denominator = vector_cross_product(v_p, v_q)
    if abs(denominator) < EPSILON: return None
    t = vector_cross_product(subtract(q1, p1), v_q) / denominator
    u = vector_cross_product(subtract(q1, p1), v_p) / denominator
    if 0.0 - EPSILON <= t <= 1.0 + EPSILON and 0.0 - EPSILON <= u <= 1.0 + EPSILON:
        return (p1[0] + t * v_p[0], p1[1] + t * v_p[1])
    return None
def is_inside(polygon, point):
    if len(polygon) < 3: return False
    for i in range(len(polygon)):
        p1, p2 = polygon[i], polygon[(i + 1) % len(polygon)];
        if cross_product(p1, p2, point) < -EPSILON: return False
    return True
def add_vertex(result_list, vertex):
    if not result_list or (abs(result_list[-1][0] - vertex[0]) > EPSILON or abs(result_list[-1][1] - vertex[1]) > EPSILON):
        result_list.append(vertex)
def intersect_convex_polygons(poly1, poly2):
    if not poly1 or len(poly1) < 3 or not poly2 or len(poly2) < 3: return []
    n1, n2 = len(poly1), len(poly2); i, j, inside = 0, 0, 0
    intersection_points, first_intersection = [], None
    for _ in range(2 * (n1 + n2) + 4):
        p_prev, p = poly1[(i - 1 + n1) % n1], poly1[i]; q_prev, q = poly2[(j - 1 + n2) % n2], poly2[j]
        intersection = intersect_segments(p_prev, p, q_prev, q)
        if intersection is not None:
            if first_intersection is None: first_intersection = intersection
            elif abs(intersection[0] - first_intersection[0]) < EPSILON and abs(intersection[1] - first_intersection[1]) < EPSILON: break
            add_vertex(intersection_points, intersection)
            if cross_product(p_prev, p, q) > EPSILON: inside = 2
            elif cross_product(q_prev, q, p) > EPSILON: inside = 1
        vec_p, vec_q = subtract(p, p_prev), subtract(q, q_prev); edge_cross = vector_cross_product(vec_p, vec_q)
        p_in_hp_q = cross_product(q_prev, q, p) >= 0; q_in_hp_p = cross_product(p_prev, p, q) >= 0
        if edge_cross >= 0:
            if q_in_hp_p:
                if inside == 1: add_vertex(intersection_points, p)
                i = (i + 1) % n1
            else:
                if inside == 2: add_vertex(intersection_points, q)
                j = (j + 1) % n2
        else:
            if p_in_hp_q:
                if inside == 2: add_vertex(intersection_points, q)
                j = (j + 1) % n2
            else:
                if inside == 1: add_vertex(intersection_points, p)
                i = (i + 1) % n1
    return intersection_points

CURSOR_SIZE = 1.5
LETTER_GEOMETRIES = {
    'M': {
        'walls': [
            [(10, 10), (20, 10), (20, 90), (10, 90)],
            [(80, 10), (90, 10), (90, 90), (80, 90)],
            [(30, 10), (40, 10), (40, 60), (30, 60)],
            [(60, 10), (70, 10), (70, 60), (60, 60)],
            [(20, 90), (30, 90), (50, 65), (45, 65)],
            [(70, 90), (80, 90), (55, 65), (50, 65)],
            [(40, 60), (45, 60), (50, 40), (45, 40)],
            [(50, 40), (55, 40), (60, 60), (55, 60)],
        ],

        'start_zone': [(20, 10), (30, 10), (30, 25), (20, 25)],
        'finish_zone': [(70, 10), (80, 10), (80, 25), (70, 25)]  
    },
    'L': {
        'walls': [
            [(20, 10), (30, 10), (30, 90), (20, 90)],
            [(30, 10), (90, 10), (90, 20), (30, 20)],
            [(45, 35), (90, 35), (90, 90), (45, 90)]
        ],
        'start_zone': [(20, 80), (45, 80), (45, 90), (20, 90)],
        'finish_zone': [(80, 20), (90, 20), (90, 35), (80, 35)]
    },
    'U': {
        'walls': [
            [(10, 10), (20, 10), (20, 90), (10, 90)],
            [(80, 10), (90, 10), (90, 90), (80, 90)],
            [(20, 10), (80, 10), (80, 20), (20, 20)],
            [(35, 35), (45, 35), (45, 90), (35, 90)],
            [(55, 35), (65, 35), (65, 90), (55, 90)],
            [(45, 35), (55, 35), (55, 45), (45, 45)],
        ],
        'start_zone': [(10, 80), (35, 80), (35, 90), (10, 90)],
        'finish_zone': [(65, 80), (90, 80), (90, 90), (65, 90)]
    }
}

game_state = {
    'walls': [], 'start_zone': None, 'finish_zone': None,
    'player_poly': None, 'player_trail': [], 'mouse_pos': (0,0),
    'status': 'ready', 'attempts': 1, 'colliding_wall_index': -1
}

def create_player_poly(center):
    points = []
    for i in range(5):
        angle = (i / 5) * 2 * math.pi + math.pi/2
        points.append((center[0] + CURSOR_SIZE * math.cos(angle), 
                       center[1] + CURSOR_SIZE * math.sin(angle)))
    return points

def setup_level(letter):
    geom = LETTER_GEOMETRIES.get(letter.upper(), LETTER_GEOMETRIES['M'])
    game_state.update({
        'walls': geom['walls'], 'start_zone': geom['start_zone'], 'finish_zone': geom['finish_zone'],
        'status': 'ready', 'colliding_wall_index': -1, 'player_trail': []
    })

def on_motion(event):
    if event.xdata is None or event.ydata is None: return
    game_state['mouse_pos'] = (event.xdata, event.ydata)

    if game_state['status'] == 'ready':
        if is_inside(game_state['start_zone'], game_state['mouse_pos']):
            game_state['status'] = 'playing'
    
    if game_state['status'] != 'playing':
        draw_game()
        return

    game_state['player_poly'] = create_player_poly(game_state['mouse_pos'])
    
    for i, wall in enumerate(game_state['walls']):
        if intersect_convex_polygons(game_state['player_poly'], wall):
            game_state['status'] = 'lose'
            if game_state['colliding_wall_index'] == -1: 
                game_state['attempts'] += 1
            game_state['colliding_wall_index'] = i
            draw_game()
            return

    game_state['player_trail'].append(game_state['mouse_pos'])
            
    if is_inside(game_state['finish_zone'], game_state['mouse_pos']):
        game_state['status'] = 'win'

    draw_game()

def on_click(event):
    if game_state['status'] == 'lose':
        setup_level(LETRA_A_JUGAR)

def draw_game():
    plt.clf()
    ax = plt.gca()
    ax.set_facecolor('white')

    ax.add_patch(Polygon(game_state['start_zone'], facecolor='limegreen', alpha=0.7))
    ax.add_patch(Polygon(game_state['finish_zone'], facecolor='deepskyblue', alpha=0.7))

    for i, wall in enumerate(game_state['walls']):
        color = 'red' if i == game_state['colliding_wall_index'] else '#0B5351'
        ax.add_patch(Polygon(wall, facecolor=color, edgecolor='black', linewidth=0.5))

    if len(game_state['player_trail']) > 1:
        trail_x, trail_y = zip(*game_state['player_trail'])
        ax.plot(trail_x, trail_y, color='lime', linewidth=CURSOR_SIZE * 1.5, alpha=0.6, solid_capstyle='round')

    if game_state['status'] == 'playing' and game_state['player_poly']:
        ax.add_patch(Polygon(game_state['player_poly'], facecolor='black'))

    if game_state['status'] == 'ready':
        ax.text(50, 50, 'Mueve el cursor a la zona de INICIO', fontsize=18, ha='center')
    elif game_state['status'] == 'win':
        ax.text(50, 50, '¡TRAZADO PERFECTO!', color='blue', fontsize=24, ha='center', bbox=dict(facecolor='white', alpha=0.8))
        ax.text(50, 40, f"Lo lograste en {game_state['attempts']} intentos.", fontsize=16, ha='center')
    elif game_state['status'] == 'lose':
        ax.text(50, 50, '¡CHOQUE!\nHaz clic para intentar de nuevo.', color='red', fontsize=24, ha='center', bbox=dict(facecolor='white', alpha=0.8))
    
    ax.set_title(f"Canal de Precisión | Intento #{game_state['attempts']}")
    ax.set_xlim(0, 100); ax.set_ylim(0, 100)
    ax.set_aspect('equal', adjustable='box')
    ax.set_xticks([]); ax.set_yticks([])
    fig.canvas.draw()

if __name__ == '__main__':
    LETRA_A_JUGAR = 'M'
    
    fig, ax = plt.subplots(figsize=(8, 8))
    fig.canvas.mpl_connect('motion_notify_event', on_motion)
    fig.canvas.mpl_connect('button_press_event', on_click)
    
    print(f"Juego 'Canal de Precisión' iniciado. Letras disponibles: {list(LETTER_GEOMETRIES.keys())}")
    print(f"Nivel actual: Letra '{LETRA_A_JUGAR}'.")
    print("Navega por el canal sin tocar las paredes.")
    
    setup_level(LETRA_A_JUGAR)
    draw_game()
    plt.show()