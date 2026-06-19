"""
座位表相邻概率模拟器 v3 — 排列枚举 × 多次座位

枚举大量 students.txt 排列（100种），每种排列生成 50 次座位表，
统计所有 5000 次模拟中每对学生坐在一起的概率。

交互式 UI：可查询任意两人名字，查看概率 + 示例排列。
"""
import secrets
import math
import json
import webbrowser
from pathlib import Path
from collections import defaultdict
import shutil
import itertools
import time

ROWS = 7
COLS = 8

# ===== 可调参数 =====
NUM_PERMUTATIONS = 100       # 枚举的排列数
SEATS_PER_PERM = 50          # 每种排列生成座位数
# ====================

TOTAL_SIMS = NUM_PERMUTATIONS * SEATS_PER_PERM

BASE = Path(__file__).parent
STUDENTS_FILE = BASE / 'students.txt'
RULES_FILE = BASE / 'rules.txt'


# ─── 1. 随机数引擎 ───
def crypto_random():
    return secrets.randbits(32) / 0x100000000


def fisher_yates_shuffle(arr, rng):
    for i in range(len(arr) - 1, 0, -1):
        j = math.floor(rng() * (i + 1))
        arr[i], arr[j] = arr[j], arr[i]


def unique_random_matrix(rows, cols, low, high, rng):
    size = rows * cols
    arr = list(range(low, high))
    fisher_yates_shuffle(arr, rng)
    selected = arr[:size]
    matrix = []
    idx = 0
    for r in range(rows):
        row = []
        for c in range(cols):
            row.append(selected[idx])
            idx += 1
        matrix.append(row)
    return matrix


# ─── 2. 文件读写 ───
def read_students(filepath):
    text = filepath.read_text(encoding='utf-8').strip()
    return [s for s in text.split() if s]


def write_students(filepath, students):
    filepath.write_text(' '.join(students), encoding='utf-8')


def parse_rules(filepath):
    rules = []
    path = Path(filepath)
    if path.exists():
        text = path.read_text(encoding='utf-8').strip()
        for line in text.split('\n'):
            line = line.strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) >= 3:
                rules.append(parts)
    return rules


# ─── 3. 单次座位生成 ───
def run_single_simulation(students, rules):
    ans = [[' ' for _ in range(COLS)] for _ in range(ROWS)]
    shuffled = list(students)
    fisher_yates_shuffle(shuffled, crypto_random)
    indices = unique_random_matrix(ROWS, COLS, 1, 57, crypto_random)
    for r in range(ROWS):
        for c in range(COLS):
            idx = indices[r][c] - 1
            if idx < len(shuffled):
                ans[r][c] = shuffled[idx]
    apply_correct_rules(ans, rules)
    pairs = set()
    for r in range(ROWS):
        for c in range(COLS):
            a = ans[r][c]
            if a == ' ':
                continue
            if c + 1 < COLS:
                b = ans[r][c + 1]
                if b != ' ':
                    pairs.add((a, b) if a < b else (b, a))
            if r + 1 < ROWS:
                b = ans[r + 1][c]
                if b != ' ':
                    pairs.add((a, b) if a < b else (b, a))
    return ans, pairs


# ─── 4. _correctRules ───
def apply_correct_rules(ans, rules):
    rows, cols = ROWS, COLS
    protected_by_rule3 = set()
    protected_by_distance = set()

    for rule in rules:
        if len(rule) < 3 or len(rule) > 6:
            continue
        mode_id = rule[0]

        if mode_id == '2':
            if len(rule) != 4:
                continue
            name = rule[1]
            tr = int(rule[2])
            tc = int(rule[3])
            pos = _find_seat(ans, name)
            if pos is None:
                continue
            cr, cc = pos
            if cr == tr and cc == tc:
                continue
            occ = ans[tr][tc]
            ans[tr][tc] = name
            ans[cr][cc] = occ if occ != name else ' '
            continue

        if mode_id == '3':
            if len(rule) != 3:
                continue
            name = rule[1]
            prob = int(rule[2])
            if prob < 0 or prob > 100:
                continue
            if crypto_random() * 100 >= prob:
                continue
            pos = _find_seat(ans, name)
            if pos is None:
                continue
            cr, cc = pos
            if cr >= 4 and cr <= 6:
                continue
            fixed_seats = {}
            for other in rules:
                if other[0] == '2' and len(other) == 4:
                    n = other[1]
                    fr = int(other[2])
                    fc = int(other[3])
                    fixed_seats[n] = (fr, fc)
            if name in fixed_seats:
                continue
            candidates = []
            for r in range(4, 7):
                for c in range(cols):
                    occ = ans[r][c]
                    if occ == name:
                        continue
                    conflict = False
                    if occ in protected_by_rule3:
                        conflict = True
                    if occ and occ != ' ' and occ in fixed_seats:
                        if fixed_seats[occ] == (r, c):
                            conflict = True
                    if not conflict:
                        candidates.append((r, c))
            if candidates:
                pick = candidates[math.floor(crypto_random() * len(candidates))]
                pr, pc = pick
                occ = ans[pr][pc]
                ans[pr][pc] = name
                ans[cr][cc] = occ if occ != name else ' '
                protected_by_rule3.add(name)
            continue

        if len(rule) != 3 and len(rule) != 4 and len(rule) != 6:
            continue
        name1, name2 = rule[1], rule[2]
        if name1 == name2:
            continue

        min_dist = 1
        max_dist = 2
        prob_val = 100
        if len(rule) == 4:
            prob_val = int(rule[3])
        elif len(rule) == 6:
            min_dist = int(rule[3])
            max_dist = int(rule[4])
            prob_val = int(rule[5])
        if prob_val >= 0 and prob_val <= 100 and crypto_random() * 100 >= prob_val:
            continue

        if mode_id == '1':
            pos1 = _find_seat(ans, name1)
            pos2 = _find_seat(ans, name2)
            if pos1 is None or pos2 is None:
                continue
            if name1 in protected_by_rule3:
                continue
            if name1 in protected_by_distance:
                continue
            r1, c1 = pos1
            r2, c2 = pos2
            dist = abs(r1 - r2) + abs(c1 - c2)
            if min_dist <= dist <= max_dist:
                continue

            fixed_seats = {}
            for other in rules:
                if other[0] == '2' and len(other) == 4:
                    n = other[1]
                    fr = int(other[2])
                    fc = int(other[3])
                    fixed_seats[n] = (fr, fc)
            if name1 in fixed_seats:
                continue

            candidates = []
            for r in range(rows):
                for c in range(cols):
                    if r == r2 and c == c2:
                        continue
                    d = abs(r - r2) + abs(c - c2)
                    if d < min_dist or d > max_dist:
                        continue
                    candidates.append((r, c))

            available = []
            already_placed = False
            for tr, tc in candidates:
                occ = ans[tr][tc]
                if occ == name1:
                    already_placed = True
                    break
                conflict = False
                if occ and occ != ' ':
                    if occ in fixed_seats and fixed_seats[occ] == (tr, tc):
                        conflict = True
                    if occ in protected_by_rule3:
                        conflict = True
                    if occ in protected_by_distance:
                        conflict = True
                if not conflict:
                    available.append((tr, tc))

            if not already_placed and available:
                pick = available[math.floor(crypto_random() * len(available))]
                tr, tc = pick
                occ = ans[tr][tc]
                ans[tr][tc] = name1
                ans[r1][c1] = occ if occ != name1 else ' '
                protected_by_distance.add(name1)

        elif mode_id == '0':
            pos1 = _find_seat(ans, name1)
            pos2 = _find_seat(ans, name2)
            if pos1 is None or pos2 is None:
                continue
            if name1 in protected_by_rule3:
                continue
            if name1 in protected_by_distance:
                continue
            r1, c1 = pos1
            r2, c2 = pos2
            dist = abs(r1 - r2) + abs(c1 - c2)
            if dist >= 2:
                continue

            fixed_seats = {}
            for other in rules:
                if other[0] == '2' and len(other) == 4:
                    n = other[1]
                    fr = int(other[2])
                    fc = int(other[3])
                    fixed_seats[n] = (fr, fc)
            if name1 in fixed_seats:
                continue

            candidates = []
            for r in range(rows):
                for c in range(cols):
                    if r == r2 and c == c2:
                        continue
                    d = abs(r - r2) + abs(c - c2)
                    if d < 2:
                        continue
                    candidates.append((r, c))

            available = []
            already_valid = False
            for tr, tc in candidates:
                occ = ans[tr][tc]
                if occ == name1:
                    already_valid = True
                    break
                conflict = False
                if occ and occ != ' ':
                    if occ in fixed_seats and fixed_seats[occ] == (tr, tc):
                        conflict = True
                    if occ in protected_by_rule3:
                        conflict = True
                    if occ in protected_by_distance:
                        conflict = True
                if not conflict:
                    available.append((tr, tc))

            if not already_valid and available:
                pick = available[math.floor(crypto_random() * len(available))]
                tr, tc = pick
                occ = ans[tr][tc]
                ans[tr][tc] = name1
                ans[r1][c1] = occ if occ != name1 else ' '
                protected_by_distance.add(name1)


def _find_seat(ans, name):
    for r in range(ROWS):
        for c in range(COLS):
            if ans[r][c] == name:
                return (r, c)
    return None


# ─── 5. 主程序 ───
def main():
    original_students = read_students(STUDENTS_FILE)
    rules = parse_rules(RULES_FILE)
    n_students = len(original_students)

    print(f"学生 {n_students} 人, 规则 {len(rules)} 条")
    print(f"枚举 {NUM_PERMUTATIONS} 种 students.txt 排列")
    print(f"每种排列生成 {SEATS_PER_PERM} 次座位表")
    print(f"总计 {TOTAL_SIMS} 次模拟")
    print("=" * 60)

    start_time = time.time()

    # 备份原始 students.txt
    backup = BASE / 'students.txt.bak'
    shutil.copy2(STUDENTS_FILE, backup)

    # 数据结构
    pair_total_count = defaultdict(int)           # (a,b) -> 总相邻次数
    pair_perm_details = defaultdict(list)         # (a,b) -> [(perm_idx, student_order), ...] (最多存3条)

    all_perm_orders = []                          # 每个排列的 students.txt 顺序

    try:
        for perm_idx in range(NUM_PERMUTATIONS):
            # ── 生成并写入当前排列 ──
            shuffled = list(original_students)
            fisher_yates_shuffle(shuffled, crypto_random)
            write_students(STUDENTS_FILE, shuffled)
            all_perm_orders.append(list(shuffled))

            # ── 从文件重新读取 ──
            current_students = read_students(STUDENTS_FILE)

            perm_pair_counts = defaultdict(int)   # 本排列内的相邻计数

            for seat_run in range(SEATS_PER_PERM):
                ans, pairs = run_single_simulation(current_students, rules)
                for pair in pairs:
                    pair_total_count[pair] += 1
                    perm_pair_counts[pair] += 1

            # ── 记录本排列的详情（只存首次出现的排列） ──
            for (a, b), cnt_in_perm in perm_pair_counts.items():
                if cnt_in_perm > 0 and len(pair_perm_details[(a, b)]) < 3:
                    pair_perm_details[(a, b)].append((perm_idx, list(shuffled)))

            if (perm_idx + 1) % 20 == 0:
                elapsed = time.time() - start_time
                print(f"  排列 {perm_idx + 1}/{NUM_PERMUTATIONS} ... ({elapsed:.0f}s)")

    finally:
        # 恢复原始 students.txt
        shutil.copy2(backup, STUDENTS_FILE)
        backup.unlink()

    elapsed = time.time() - start_time
    print(f"\n完成! 耗时 {elapsed:.1f}s")
    print(f"共出现 {len(pair_total_count)} 对同桌组合")
    print("=" * 60)

    # 排序
    sorted_pairs = sorted(pair_total_count.items(), key=lambda x: -x[1])

    # 基线概率 (每次座位表有 91 条相邻边, 总可能 pair = C(n,2))
    total_edges_per_sim = (ROWS - 1) * COLS + ROWS * (COLS - 1)  # = 91
    total_possible_pairs = n_students * (n_students - 1) // 2    # = 1540
    baseline_prob_per_sim = total_edges_per_sim / total_possible_pairs  # ≈ 5.9%
    baseline_count = TOTAL_SIMS * baseline_prob_per_sim

    # 生成 HTML
    html_path = BASE / 'simulation_report.html'
    generate_html(html_path, original_students, rules, sorted_pairs,
                  pair_total_count, pair_perm_details, all_perm_orders,
                  TOTAL_SIMS, ROWS, COLS)

    print(f"📊 报告已生成: {html_path}")
    webbrowser.open(str(html_path))


# ─── 6. HTML 生成 ───
def generate_html(path, students, rules, sorted_pairs,
                  pair_total_count, pair_perm_details, all_perm_orders,
                  total_sims, rows, cols):

    rules_desc = []
    for r in rules:
        if r[0] == '2':
            rules_desc.append(f"固定: {r[1]}→({int(r[2])+1},{int(r[3])+1})")
        elif r[0] == '3':
            rules_desc.append(f"概率行: {r[1]} {r[2]}% 行5-7")
        elif r[0] == '1':
            if len(r) == 4:
                rules_desc.append(f"距离: {r[1]}-{r[2]} 距1-2, {r[3]}%")
            elif len(r) == 6:
                rules_desc.append(f"距离: {r[1]}-{r[2]} 距{r[3]}-{r[4]}, {r[5]}%")
        elif r[0] == '0':
            rules_desc.append(f"不相邻: {r[1]}-{r[2]}")

    # 准备 pair 数据
    all_pairs_data = []
    for (a, b), cnt in sorted_pairs:
        details = pair_perm_details.get((a, b), [])
        sample_data = [{'permIdx': idx, 'order': order} for idx, order in details]
        all_pairs_data.append({
            'a': a, 'b': b, 'cnt': cnt,
            'samples': sample_data
        })

    # 学生总相邻次数
    student_adj_count = defaultdict(int)
    for (a, b), cnt in pair_total_count.items():
        student_adj_count[a] += cnt
        student_adj_count[b] += cnt
    student_rank = sorted(student_adj_count.items(), key=lambda x: -x[1])

    baseline_percent = 100 * ((ROWS - 1) * COLS + ROWS * (COLS - 1)) / (len(students) * (len(students) - 1) // 2)

    json_data = json.dumps({
        'students': students,
        'pairs': all_pairs_data,
        'studentRank': [(n, c) for n, c in student_rank],
        'totalSims': total_sims,
        'baselinePct': round(baseline_percent, 2),
        'allPermOrders': all_perm_orders,
        'numPerms': len(all_perm_orders),
        'seatsPerPerm': total_sims // len(all_perm_orders) if all_perm_orders else 0
    }, ensure_ascii=False)

    NUM_PERMUTATIONS = len(all_perm_orders)
    SEATS_PER_PERM = total_sims // NUM_PERMUTATIONS if NUM_PERMUTATIONS else 0

    html = f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>排列枚举 × 多次座位 · 相邻概率报告</title>
<style>
:root {{
    --bg: #f0f2f5;
    --card: #fff;
    --text: #1a1a2e;
    --text2: #6b7280;
    --primary: #4f46e5;
    --primary-light: #eef2ff;
    --border: #e5e7eb;
    --radius: 12px;
    --shadow: 0 1px 3px rgba(0,0,0,0.08);
}}
@media (prefers-color-scheme: dark) {{
    :root {{
        --bg: #0f172a;
        --card: #1e293b;
        --text: #e2e8f0;
        --text2: #94a3b8;
        --primary-light: #1e1b4b;
        --border: #334155;
    }}
}}
* {{ margin:0; padding:0; box-sizing:border-box; }}
body {{
    font-family: 'Segoe UI', 'PingFang SC', 'Microsoft YaHei', sans-serif;
    background: var(--bg);
    color: var(--text);
}}
.layout {{ max-width: 1400px; margin: 0 auto; padding: 24px 20px; }}
h1 {{
    font-size: 1.5rem;
    font-weight: 700;
    background: linear-gradient(135deg, var(--primary), #7c3aed);
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    margin-bottom: 2px;
}}
.subtitle {{ color: var(--text2); font-size: 0.85rem; margin-bottom: 18px; }}

/* stats */
.stats-row {{
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(130px, 1fr));
    gap: 10px;
    margin-bottom: 16px;
}}
.stat-card {{
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 10px;
    padding: 14px;
    text-align: center;
    box-shadow: var(--shadow);
}}
.stat-num {{ font-size: 1.5rem; font-weight: 700; color: var(--primary); }}
.stat-lbl {{ font-size: 0.78rem; color: var(--text2); margin-top: 2px; }}

/* query */
.query-panel {{
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: var(--radius);
    padding: 18px;
    margin-bottom: 16px;
    box-shadow: var(--shadow);
}}
.query-row {{
    display: flex;
    gap: 12px;
    align-items: center;
    flex-wrap: wrap;
}}
.query-input-wrap {{ flex: 1; min-width: 170px; }}
.query-input-wrap label {{ display: block; font-size: 0.78rem; font-weight: 600; color: var(--text2); margin-bottom: 3px; }}
.query-input {{
    width: 100%;
    padding: 9px 12px;
    border: 2px solid var(--border);
    border-radius: 8px;
    font-size: 0.9rem;
    background: var(--card);
    color: var(--text);
    transition: border-color 0.2s;
}}
.query-input:focus {{ outline: none; border-color: var(--primary); }}
.query-result {{
    margin-top: 12px;
    padding: 12px 16px;
    border-radius: 10px;
    background: var(--primary-light);
    display: none;
}}
.query-result.show {{ display: block; }}
.qpct {{ font-size: 2.4rem; font-weight: 800; color: var(--primary); }}

/* table */
.table-card {{
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: var(--radius);
    box-shadow: var(--shadow);
    overflow: hidden;
}}
.table-scroll {{ overflow-x: auto; max-height: 480px; overflow-y: auto; }}
table {{ width: 100%; border-collapse: collapse; font-size: 0.85rem; }}
th {{
    background: var(--bg);
    padding: 9px 11px;
    text-align: left;
    font-weight: 600;
    border-bottom: 2px solid var(--border);
    white-space: nowrap;
    position: sticky;
    top: 0;
    z-index: 2;
}}
td {{ padding: 8px 11px; border-bottom: 1px solid var(--border); }}
tr.clickable {{ cursor: pointer; }}
tr.clickable:hover td {{ background: rgba(79,70,229,0.06) !important; }}

.bar {{ display: inline-block; height: 6px; border-radius: 3px; margin-left: 4px; vertical-align: middle; }}
.bar-red {{ background: linear-gradient(90deg, #ef4444, #f97316); }}
.bar-orange {{ background: linear-gradient(90deg, #f97316, #eab308); }}
.bar-green {{ background: linear-gradient(90deg, #22c55e, #4ade80); }}
.badge {{
    display: inline-block;
    padding: 2px 7px;
    border-radius: 7px;
    font-size: 0.7rem;
    font-weight: 600;
}}
.badge-red {{ background: #fef2f2; color: #dc2626; }}
.badge-orange {{ background: #fff7ed; color: #ea580c; }}
.badge-green {{ background: #f0fdf4; color: #16a34a; }}

/* detail */
.detail-panel {{
    display: none;
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: var(--radius);
    padding: 16px;
    margin-top: 14px;
    box-shadow: var(--shadow);
}}
.detail-panel.show {{ display: block; }}
.order-sample {{
    font-family: 'Consolas', monospace;
    font-size: 0.75rem;
    padding: 7px 10px;
    background: var(--bg);
    border-radius: 6px;
    margin: 3px 0;
    word-break: break-all;
    line-height: 1.5;
}}
.order-sample .hl {{
    background: #fef08a;
    color: #1a1a2e;
    padding: 0 2px;
    border-radius: 2px;
}}
.rule-tag {{
    display: inline-block;
    padding: 2px 8px;
    background: var(--primary-light);
    color: var(--primary);
    border-radius: 5px;
    font-size: 0.75rem;
    margin: 1px 3px;
}}
.filter-input {{
    padding: 7px 12px;
    border: 1px solid var(--border);
    border-radius: 6px;
    font-size: 0.82rem;
    background: var(--card);
    color: var(--text);
}}
</style>
</head>
<body>
<div class="layout">
    <h1>🔬 排列枚举 × 多次座位 — 相邻概率分析</h1>
    <p class="subtitle">
        枚举 {NUM_PERMUTATIONS} 种 students.txt 排列 · 每种生成 {SEATS_PER_PERM} 次座位表 · 总计 {total_sims} 次模拟
    </p>

    <div class="stats-row">
        <div class="stat-card"><div class="stat-num">{len(students)}</div><div class="stat-lbl">学生</div></div>
        <div class="stat-card"><div class="stat-num">{len(rules)}</div><div class="stat-lbl">规则</div></div>
        <div class="stat-card"><div class="stat-num">{NUM_PERMUTATIONS}</div><div class="stat-lbl">排列数</div></div>
        <div class="stat-card"><div class="stat-num">{total_sims}</div><div class="stat-lbl">总模拟次数</div></div>
        <div class="stat-card"><div class="stat-num">{len(pair_total_count)}</div><div class="stat-lbl">出现组合</div></div>
    </div>

    <!-- 🏆 最高相邻概率组合 -->
    <div class="card" style="background:linear-gradient(135deg,#fef2f2,#fff7ed);border:2px solid #fca5a5;border-radius:var(--radius);padding:16px 20px;margin-bottom:14px;box-shadow:var(--shadow);">
        <div style="display:flex;align-items:center;gap:12px;flex-wrap:wrap;">
            <span style="font-size:1.6rem;">🏆</span>
            <div>
                <div style="font-size:0.8rem;font-weight:600;color:#b91c1c;">最高相邻概率组合</div>
                <div id="topPairDisplay" style="font-size:1.2rem;font-weight:700;">加载中...</div>
            </div>
            <div style="margin-left:auto;text-align:right;" id="topPairStat">
                <div style="font-size:1.8rem;font-weight:800;color:#dc2626;" id="topPairPct">-</div>
                <div style="font-size:0.75rem;color:#b91c1c;" id="topPairCount">-</div>
            </div>
        </div>
        <div style="margin-top:8px;display:flex;flex-wrap:wrap;gap:4px;" id="topPairTags"></div>
    </div>

    <!-- 规则 -->
    <div style="display:flex;flex-wrap:wrap;gap:3px;margin-bottom:14px;">
        {"".join(f'<span class="rule-tag">{d}</span>' for d in rules_desc)}
    </div>

    <!-- 查询 -->
    <div class="query-panel">
        <div class="query-row">
            <div class="query-input-wrap">
                <label>👤 学生 A</label>
                <input class="query-input" id="qA" list="sl" placeholder="输入姓名..." oninput="onQuery()">
            </div>
            <div style="font-size:1.3rem; color:var(--text2); padding-top:16px;">↔</div>
            <div class="query-input-wrap">
                <label>👤 学生 B</label>
                <input class="query-input" id="qB" list="sl" placeholder="输入姓名..." oninput="onQuery()">
            </div>
            <div style="padding-top:16px;">
                <button onclick="clearQ()" style="padding:8px 16px; border:1px solid var(--border); border-radius:6px; background:var(--card); cursor:pointer; color:var(--text2);">清空</button>
            </div>
        </div>
        <datalist id="sl">{"".join(f'<option value="{s}">' for s in students)}</datalist>
        <div class="query-result" id="qr">
            <div style="display:flex; align-items:baseline; gap:10px; flex-wrap:wrap;">
                <span id="ql" style="font-weight:600;"></span>
                <span class="qpct" id="qp"></span>
                <span style="color:var(--text2);font-size:0.82rem;" id="qc"></span>
                <span id="qb"></span>
            </div>
            <div class="detail" id="qd"></div>
        </div>
    </div>

    <!-- table -->
    <div class="table-card">
        <div style="padding:12px 14px 0;display:flex;align-items:center;gap:10px;flex-wrap:wrap;">
            <span style="font-weight:600;font-size:0.9rem;">📊 全部组合</span>
            <input class="filter-input" id="fa" placeholder="筛 A..." oninput="filter()">
            <input class="filter-input" id="fb" placeholder="筛 B..." oninput="filter()">
            <label style="font-size:0.78rem;color:var(--text2);display:flex;align-items:center;gap:3px;">
                <input type="checkbox" id="onlySig" onchange="filter()"> 仅显著
            </label>
        </div>
        <div class="table-scroll">
            <table>
                <thead><tr><th>#</th><th>A</th><th>B</th><th>次数</th><th>概率</th><th>倍数</th><th>强度</th></tr></thead>
                <tbody id="tb"></tbody>
            </table>
        </div>
    </div>

    <div class="detail-panel" id="dp">
        <h3 id="dt" style="font-size:0.95rem;margin-bottom:8px;"></h3>
        <div id="dc"></div>
    </div>

    <div style="text-align:center;color:var(--text2);font-size:0.75rem;padding:20px 0 10px;">
        {NUM_PERMUTATIONS} 种排列 × {SEATS_PER_PERM} 次座位 · 引擎: Python secrets.randbits(32) ≡ crypto.getRandomValues
    </div>
</div>

<script>
const D = {json_data};
const stu = D.students, pairs = D.pairs, TS = D.totalSims, BP = D.baselinePct;
const nrm = s => s.trim().replace(/\\s+/g,'');
function gp(a,b) {{
    if(!a||!b)return null;
    const ka=nrm(a),kb=nrm(b);
    return pairs.find(p=>(nrm(p.a)===ka&&nrm(p.b)===kb)||(nrm(p.a)===kb&&nrm(p.b)===ka))||null;
}}
function onQuery() {{
    const a=document.getElementById('qA').value, b=document.getElementById('qB').value, el=document.getElementById('qr');
    if(!a||!b){{el.classList.remove('show');return;}}
    const p=gp(a,b);
    if(!p){{
        document.getElementById('ql').textContent=a+' ↔ '+b;
        document.getElementById('qp').textContent='0%';
        document.getElementById('qc').textContent='(0/'+TS+')';
        document.getElementById('qb').innerHTML='<span class="badge badge-green">未出现</span>';
        document.getElementById('qd').textContent='';
        el.classList.add('show'); return;
    }}
    const r=p.cnt/TS*100, m=(r/BP).toFixed(1);
    document.getElementById('ql').textContent=p.a+' ↔ '+p.b;
    document.getElementById('qp').textContent=r.toFixed(1)+'%';
    document.getElementById('qc').textContent='('+p.cnt+'/'+TS+')';
    let bg='<span class="badge badge-green">正常</span>';
    if(r>=90) bg='<span class="badge badge-red">强制同桌</span>';
    else if(r>=30) bg='<span class="badge badge-red">极高</span>';
    else if(r>=15) bg='<span class="badge badge-orange">偏高</span>';
    else if(r>=8) bg='<span class="badge badge-orange">略高</span>';
    document.getElementById('qb').innerHTML=bg;
    document.getElementById('qd').textContent='基线 '+BP.toFixed(1)+'% · 实际 ×'+mult+' 倍';
    el.classList.add('show');
}}
function clearQ(){{document.getElementById('qA').value='';document.getElementById('qB').value='';document.getElementById('qr').classList.remove('show');}}
function filter(){{
    const fa=document.getElementById('fa').value.trim().toLowerCase();
    const fb=document.getElementById('fb').value.trim().toLowerCase();
    const os=document.getElementById('onlySig').checked;
    const tb=document.getElementById('tb'); tb.innerHTML='';
    let idx=0;
    pairs.forEach(p=>{{
        const na=p.a.toLowerCase(), nb=p.b.toLowerCase();
        if(fa&&!na.includes(fa)&&!nb.includes(fa))return;
        if(fb&&!na.includes(fb)&&!nb.includes(fb))return;
        if(os&&p.cnt<TS*BP/100*2)return;
        idx++;
        const r=p.cnt/TS*100, m=(r/BP).toFixed(1), bw=Math.min(100,r*2.5);
        let bc='badge-green',bt='正常',bl='bar-green';
        if(r>=90){{bc='badge-red';bt='强制';bl='bar-red';}}else if(r>=30){{bc='badge-red';bt='极高';bl='bar-red';}}else if(r>=15){{bc='badge-orange';bt='偏高';bl='bar-orange';}}else if(r>=8){{bc='badge-orange';bt='略高';bl='bar-orange';}}
        const tr=document.createElement('tr'); tr.className='clickable';
        tr.onclick=()=>showDetail(p);
        tr.innerHTML='<td style="color:var(--text2);font-size:0.75rem;">'+idx+'</td><td><strong>'+p.a+'</strong></td><td><strong>'+p.b+'</strong></td><td>'+p.cnt+'/'+TS+'</td><td>'+r.toFixed(1)+'%<span class="bar '+bl+'" style="width:'+bw+'px"></span></td><td>×'+m+'</td><td><span class="badge '+bc+'">'+bt+'</span></td>';
        tb.appendChild(tr);
    }});
}}
function showDetail(p){{
    const pnl=document.getElementById('dp'), ttl=document.getElementById('dt'), ct=document.getElementById('dc');
    ttl.textContent='📋 '+p.a+' ↔ '+p.b+' 详情';
    let sh='';
    const ss=p.samples||[];
    const maxS=Math.min(5,ss.length);
    for(let i=0;i<maxS;i++){{
        const s=ss[i], order=D.allPermOrders[s.permIdx]||[];
        const hl=order.map(n=>{{if(n===p.a||n===p.b)return'<span class="hl">'+n+'</span>';return n;}}).join(' ');
        sh+='<div style="margin-bottom:5px;"><div style="font-size:0.72rem;color:var(--text2);">排列 #'+(s.permIdx+1)+' · students.txt:</div><div class="order-sample">'+hl+'</div></div>';
    }}
    if(ss.length>maxS) sh+='<div style="font-size:0.75rem;color:var(--text2);">… 还有 '+(ss.length-maxS)+' 个排列中的相邻记录</div>';
    ct.innerHTML='<div style="display:flex;gap:16px;flex-wrap:wrap;margin-bottom:10px;"><div><strong>概率</strong><br><span style="font-size:1.6rem;font-weight:700;color:var(--primary);">'+(p.cnt/TS*100).toFixed(1)+'%</span></div><div><strong>次数</strong><br><span style="font-size:1.3rem;font-weight:600;">'+p.cnt+'/'+TS+'</span></div><div><strong>基线</strong><br><span style="font-size:1.3rem;font-weight:600;">≈'+BP.toFixed(1)+'%</span></div></div><h4 style="margin:8px 0 4px;font-size:0.85rem;">📄 相邻时的 students.txt 排列样本</h4>'+sh;
    pnl.classList.add('show');
    pnl.scrollIntoView({{behavior:'smooth',block:'start'}});
}}
function showTopPairs() {{
    // 找到最大次数
    let maxCnt = 0;
    for (const p of pairs) {{
        if (p.cnt > maxCnt) maxCnt = p.cnt;
    }}
    const topPairs = pairs.filter(p => p.cnt === maxCnt);
    const topCount = topPairs.length;

    // 显示
    const display = document.getElementById('topPairDisplay');
    if (topCount === 1) {{
        display.textContent = topPairs[0].a + ' ↔ ' + topPairs[0].b;
    }} else {{
        display.textContent = '共 ' + topCount + ' 对组合并列第一';
    }}

    document.getElementById('topPairPct').textContent = (maxCnt / TS * 100).toFixed(1) + '%';
    document.getElementById('topPairCount').textContent = maxCnt + ' / ' + TS + ' 次';

    // 显示所有顶级组合标签
    const tags = document.getElementById('topPairTags');
    tags.innerHTML = '';
    for (const p of topPairs) {{
        const tag = document.createElement('span');
        tag.style.cssText = 'display:inline-block;padding:4px 12px;background:#fef2f2;color:#dc2626;border-radius:6px;font-size:0.82rem;font-weight:600;cursor:pointer;border:1px solid #fca5a5;';
        tag.textContent = p.a + ' ↔ ' + p.b;
        tag.onclick = () => showDetail(p);
        tags.appendChild(tag);
    }}

    // 如果只有1个顶级组合，也显示它的详情
    if (topPairs.length === 1) {{
        showDetail(topPairs[0]);
    }}
}}
showTopPairs();
filter();
document.getElementById('qA').addEventListener('keydown',e=>{{if(e.key==='Enter')document.getElementById('qB').focus();}});
document.getElementById('qB').addEventListener('keydown',e=>{{if(e.key==='Enter')document.getElementById('qA').focus();}});
</script>
</body>
</html>'''

    path.write_text(html, encoding='utf-8')


if __name__ == '__main__':
    main()
