#!/usr/bin/env python3
import re
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple

# UTILIDADES / TIPOS GENERALES
VALID_BODY_CHARS = set("abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ")
EPS_SYMBOLS = {"ε", "ϵ"}
Productions = Dict[str, Set[str]]

def die(msg: str) -> None:
    print(f"ERROR: {msg}", file=sys.stderr); sys.exit(1)

def banner(title: str) -> None:
    print(f"\n>>> {title} <<<\n")

def subbanner(title: str) -> None:
    print(f"\n-- {title} --\n")

def label_pair(label: str, value: str) -> None:
    print(f"{label}: {value}")

def is_terminal(ch: str) -> bool:
    return ch.islower() or ch.isdigit()

def is_nonterminal(ch: str) -> bool:
    return ch.isupper()

# PARSER Y PRETTY PRINTER
def parse_grammar_file(path: Path) -> Tuple[str, Productions]:
    line_regex = re.compile(r'^\s*([A-Z])\s*->\s*([^\n]+?)\s*$')
    prods: Productions = {}
    start_symbol: str = None

    with path.open("r", encoding="utf-8") as f:
        for idx, raw in enumerate(f, start=1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            m = line_regex.match(line)
            if not m:
                die(f"{path.name}:{idx}: sintaxis inválida. Esperado 'A -> ...'. Recibido: {line}")

            lhs = m.group(1)
            rhs = m.group(2)
            if start_symbol is None:
                start_symbol = lhs

            bodies = [b.strip() for b in rhs.split("|")]
            cleaned: List[str] = []
            for b in bodies:
                if not b:
                    die(f"{path.name}:{idx}: cuerpo vacío entre '|'.")
                if b in EPS_SYMBOLS:
                    cleaned.append("ε")
                    continue
                for ch in b:
                    if ch not in VALID_BODY_CHARS:
                        die(f"{path.name}:{idx}: símbolo inválido '{ch}' en cuerpo '{b}'.")
                cleaned.append(b)
            prods.setdefault(lhs, set()).update(cleaned)

    if start_symbol is None:
        die(f"{path.name}: no hay producciones.")
    return start_symbol, prods

def pretty_grammar(start: str, prods: Productions) -> str:
    lines = []
    order = sorted(prods.keys(), key=lambda X: (X != start, X))
    for A in order:
        bodies = sorted(prods[A], key=lambda s: (s == "ε", s))
        rhs = " | ".join(bodies) if bodies else "∅"
        lines.append(f"{A} -> {rhs}")
    return "\n".join(lines)

# PARTE 1: PROBLEMA 1 — ELIMINACIÓN DE ε-PRODUCCIONES
def find_nullable(start: str, prods: Productions) -> Set[str]:
    nullable: Set[str] = set()
    for A, bodies in prods.items():
        if "ε" in bodies:
            nullable.add(A)
    changed = True
    while changed:
        changed = False
        for A, bodies in prods.items():
            if A in nullable: 
                continue
            for b in bodies:
                if b == "ε":
                    nullable.add(A); changed = True; break
                ok = True
                for ch in b:
                    if is_terminal(ch): ok = False; break
                    if is_nonterminal(ch) and ch not in nullable: ok = False; break
                if ok:
                    nullable.add(A); changed = True; break
    return nullable

def eliminate_epsilon(start: str, prods: Productions, keep_start_epsilon: bool = True) -> Tuple[str, Productions, List[str]]:
    steps: List[str] = []
    nullable = find_nullable(start, prods)
    steps.append(f"Nullable (A ⇒* ε): {', '.join(sorted(nullable)) or '∅'}")

    new_prods: Productions = {A: set() for A in prods.keys()}
    for A, bodies in prods.items():
        for b in bodies:
            if b == "ε":
                continue
            positions = [i for i, ch in enumerate(b) if is_nonterminal(ch) and ch in nullable]
            m = len(positions)
            generated: Set[str] = set()

            for mask in range(1 << m):
                out = []
                for i, ch in enumerate(b):
                    if i in positions:
                        pos_idx = positions.index(i)
                        drop = (mask >> pos_idx) & 1
                        if drop: 
                            continue
                    out.append(ch)
                candidate = "".join(out)
                if candidate == "":
                    if A == start and keep_start_epsilon:
                        generated.add("ε")
                else:
                    generated.add(candidate)

            if m > 0:
                steps.append(f"{A} -> {b}  ⇒  " + " | ".join(sorted(generated)))
            new_prods[A].update(generated if generated else {b})

    if keep_start_epsilon and start in nullable:
        new_prods[start].add("ε")
    for A in list(new_prods.keys()):
        if A != start:
            new_prods[A].discard("ε")
    return start, new_prods, steps

# PARTE 2: PROBLEMA 2 — (a) UNITARIAS, (b) INÚTILES, (c) CNF
def eliminate_unit_productions(start: str, prods: Productions) -> Tuple[str, Productions, List[str]]:
    steps: List[str] = []
    nts = list(prods.keys())

    unit: Dict[str, Set[str]] = {A: set([A]) for A in nts}
    changed = True
    while changed:
        changed = False
        for A in nts:
            for b in prods.get(A, set()):
                if len(b) == 1 and is_nonterminal(b) and b not in unit[A]:
                    unit[A].add(b); changed = True
            for B in list(unit[A]):
                unit[A] |= unit.get(B, set())

    new_prods: Productions = {A: set() for A in nts}
    for A in nts:
        for B in unit[A]:
            for body in prods.get(B, set()):
                if len(body) == 1 and is_nonterminal(body):
                    continue
                new_prods[A].add(body)
        steps.append(f"Clausura unitaria({A}) = {{{', '.join(sorted(unit[A]))}}}")
    return start, new_prods, steps

def generating_nonterminals(prods: Productions) -> Set[str]:
    gen: Set[str] = set()
    changed = True
    while changed:
        changed = False
        for A, bodies in prods.items():
            if A in gen: continue
            for b in bodies:
                ok = True
                for ch in b:
                    if is_terminal(ch): continue
                    if is_nonterminal(ch) and ch not in gen:
                        ok = False; break
                if ok:
                    gen.add(A); changed = True; break
    return gen

def reachable_nonterminals(start: str, prods: Productions) -> Set[str]:
    reach: Set[str] = {start}
    changed = True
    while changed:
        changed = False
        for A in list(reach):
            for b in prods.get(A, set()):
                for ch in b:
                    if is_nonterminal(ch) and ch not in reach:
                        reach.add(ch); changed = True
    return reach

def remove_useless_symbols(start: str, prods: Productions) -> Tuple[str, Productions, List[str]]:
    steps: List[str] = []
    gen = generating_nonterminals(prods)
    steps.append(f"No terminales generadores: {', '.join(sorted(gen)) or '∅'}")

    prods_gen: Productions = {}
    for A, bodies in prods.items():
        if A not in gen: continue
        kept = set()
        for b in bodies:
            if all(is_terminal(ch) or ch in gen for ch in b):
                kept.add(b)
        prods_gen[A] = kept

    reach = reachable_nonterminals(start, prods_gen)
    steps.append(f"No terminales alcanzables: {', '.join(sorted(reach)) or '∅'}")

    prods_final: Productions = {}
    for A, bodies in prods_gen.items():
        if A in reach:
            prods_final[A] = set(bodies)
    if start not in prods_final:
        prods_final[start] = set()
    return start, prods_final, steps

def fresh_var(used: Set[str], base: str = "X") -> str:
    i = 1
    while True:
        cand = f"{base}{i}"
        if cand not in used:
            used.add(cand)
            return cand
        i += 1

def to_cnf(start: str, prods: Productions) -> Tuple[str, Productions, List[str]]:
    steps: List[str] = []
    used = set(prods.keys())

    term_var: Dict[str, str] = {}
    cnf1: Productions = {A: set() for A in prods.keys()}
    for A, bodies in prods.items():
        for b in bodies:
            if b == "ε" and A != start:
                continue
            if len(b) >= 2:
                new_body = []
                for ch in b:
                    if is_terminal(ch):
                        if ch not in term_var:
                            candidate = ch.upper()
                            if candidate in used or len(candidate) != 1 or not candidate.isupper():
                                candidate = fresh_var(used, base=f"T{ch}")
                            used.add(candidate)
                            term_var[ch] = candidate
                        new_body.append(term_var[ch])
                    else:
                        new_body.append(ch)
                cnf1[A].add("".join(new_body))
            else:
                cnf1[A].add(b)
    for a, Va in term_var.items():
        cnf1.setdefault(Va, set()).add(a)
        steps.append(f"Terminal lift: {Va} -> {a}")

    cnf2: Productions = {A: set() for A in cnf1.keys()}
    used = set(cnf1.keys())
    for A, bodies in cnf1.items():
        for b in bodies:
            if b == "ε" and A == start:
                cnf2[A].add("ε"); continue
            if len(b) <= 2:
                cnf2[A].add(b); continue
            symbols = list(b)
            prev_left = A
            for i in range(len(symbols) - 2):
                X = symbols[i]
                Y = fresh_var(used, base="Y")
                cnf2.setdefault(prev_left, set()).add(X + Y)
                steps.append(f"Binaria: {prev_left} -> {X}{Y}")
                prev_left = Y
            cnf2.setdefault(prev_left, set()).add(symbols[-2] + symbols[-1])
            steps.append(f"Binaria: {prev_left} -> {symbols[-2]}{symbols[-1]}")
    return start, cnf2, steps

# MAIN
def main(argv: List[str]) -> int:
    import argparse
    p = argparse.ArgumentParser(description="Parte 1 (ε) y Parte 2 (unitarias, inútiles, CNF).")
    p.add_argument("files", nargs="*", help="Archivos .txt con gramáticas.")
    p.add_argument("--no-start-epsilon", action="store_true",
                   help="No conservar S->ε aunque S sea anulable.")
    args = p.parse_args(argv)

    if not args.files:
        default = Path("grammar1.txt")
        if default.exists():
            args.files = [str(default)]
            print("[INFO] Usando 'grammar1.txt' por defecto.\n")
        else:
            print("ERROR: No hay archivo de gramática.")
            return 2

    for idx, file_path in enumerate(args.files, start=1):
        path = Path(file_path)
        banner(f"CFG #{idx} — Archivo: {path.name}")

        S, G = parse_grammar_file(path)
        subbanner("Gramática original")
        label_pair("Símbolo inicial", S)
        print(pretty_grammar(S, G))

        # Parte 1
        banner("PARTE 1 — Problema 1: Eliminación de ε-producciones")
        keep_start = not args.no_start_epsilon
        S1, G1, steps1 = eliminate_epsilon(S, G, keep_start_epsilon=keep_start)
        subbanner("Pasos (Parte 1)")
        for st in steps1: print(st)
        subbanner("Resultado Parte 1 (sin ε-producciones)")
        print(pretty_grammar(S1, G1))

        # Parte 2
        banner("PARTE 2 — Problema 2: (a) Unitarias, (b) Inútiles, (c) CNF")

        subbanner("Parte 2 (a) — Eliminar unitarias")
        S2a, G2a, steps2a = eliminate_unit_productions(S1, G1)
        for st in steps2a: print(st)
        print("\nTras (a):\n" + pretty_grammar(S2a, G2a))

        subbanner("Parte 2 (b) — Eliminar símbolos inútiles")
        S2b, G2b, steps2b = remove_useless_symbols(S2a, G2a)
        for st in steps2b: print(st)
        print("\nTras (b):\n" + pretty_grammar(S2b, G2b))

        subbanner("Parte 2 (c) — Conversión a CNF")
        S2c, G2c, steps2c = to_cnf(S2b, G2b)
        for st in steps2c: print(st)
        print("\nResultado final (CNF):\n" + pretty_grammar(S2c, G2c))

    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
