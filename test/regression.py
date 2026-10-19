import functools
import itertools
import random
import subprocess
import sys


executable = sys.argv[1]
checks = 0


def invoke(*args, status=0):
    global checks
    result = subprocess.run(
        [executable, *args], capture_output=True, text=True, timeout=30
    )
    checks += 1
    assert result.returncode == status, (args, result.returncode, result.stdout, result.stderr)
    return result.stdout.rstrip("\n")


def expect(args, output, status=0):
    actual = invoke(*args, status=status)
    assert actual == output, (args, actual, output)


def render(r):
    tag = r[0]
    if tag == "zero":
        return "#"
    if tag == "epsilon":
        return "@"
    if tag == "literal":
        return r[1]
    if tag == "star":
        return "(" + render(r[1]) + ")*"
    separator = "|" if tag == "union" else ""
    return "(" + render(r[1]) + separator + render(r[2]) + ")"


def concatenate(lhs, rhs, bound):
    return frozenset(x + y for x in lhs for y in rhs if len(x) + len(y) <= bound)


@functools.cache
def language(r, bound):
    tag = r[0]
    if tag == "zero":
        return frozenset()
    if tag == "epsilon":
        return frozenset([""])
    if tag == "literal":
        return frozenset([r[1]]) if bound else frozenset()
    lhs = language(r[1], bound)
    if tag == "union":
        return lhs | language(r[2], bound)
    if tag == "concat":
        return concatenate(lhs, language(r[2], bound), bound)
    result = frozenset([""])
    while True:
        expanded = result | concatenate(result, lhs, bound)
        if result == expanded:
            return result
        result = expanded


fixed = [
    ("#", "", False),
    ("#", "a", False),
    ("@", "", True),
    ("@", "a", False),
    ("a", "a", True),
    ("a", "b", False),
    ("aaaa", "aaab", False),
    ("a", "aa", False),
    ("((a|b)|a)", "b", True),
    ("ab", "ab", True),
    ("ab", "a", False),
    ("a*", "", True),
    ("(@|a)*", "aaa", True),
    ("(#|@)*", "a", False),
    ("(a|b)*abb", "aabb", True),
    ("(a|b)*abb", "abab", False),
    (r"\|\*\(\)\@\#\\", "|*()@#\\", True),
    ("λ(🙂|λ)*", "λ🙂λ", True),
    ("a b", "a b", True),
]
for regex, word, accepted in fixed:
    expect(("match", regex, word), str(accepted).lower())

expect(("match-many", "(a|b)*abb", "aabb", "abab", "abb"), "true\nfalse\ntrue")
expect(("match-many", "@", "", "a"), "true\nfalse")
expect(("match-many", "a|", "a"), "parse error at offset 2: expected expression", 1)

malformed = ["", "()", "(", ")", "a)", "(a", "|a", "a|", "a||b", "*a", "a(|b)", "a\\"]
for regex in malformed:
    error = invoke("match", regex, "", status=1)
    assert error.startswith("parse error at offset "), (regex, error)
expect(("match", "a||b", ""), "parse error at offset 2: missing left operand of union", 1)
assert invoke("unknown", status=1).startswith("usage: rumus")
assert invoke("--help").startswith("usage: rumus")

for char in [chr(n) for n in range(32, 127)] + ["λ", "🙂", "é"]:
    expect(("match", "\\" + char, char), "true")
    expect(("match", "(\\" + char + ")", char), "true")

normalizations = [
    ("#|a", "a"),
    ("a|#", "a"),
    ("a#", "#"),
    ("#a", "#"),
    ("@a@", "a"),
    ("(a|b)|(b|a)", "a|b"),
    ("((a*)*)*", "a*"),
    ("#*", "@"),
    ("@*", "@"),
]
for regex, normalized in normalizations:
    expect(("normalize", regex), normalized)

pairs = [
    ("(a|b)*", "(b|a)*", True),
    ("a(b|@)", "ab|a", True),
    ("(a|b)c", "ac|bc", True),
    ("a*", "@|aa*", True),
    ("(ab)*a", "a(ba)*", True),
    ("(a*b*)*", "(a|b)*", True),
    ("(abcdefghij)*", "@|abcdefghij(abcdefghij)*", True),
    ("(@|a)*", "a*", True),
    ("#*", "@", True),
    ("#", "a#", True),
    ("a*b", "ab*", False),
    ("@", "#", False),
    ("a", "b", False),
    ("aaaa", "aaab", False),
    ("a*", "aa*", False),
    ("(ab)*", "(ba)*", False),
    ("λ*", "🙂*", False),
]
for lhs, rhs, equivalent in pairs:
    result = invoke("equivalent", lhs, rhs)
    if equivalent:
        assert result == "equivalent", (lhs, rhs, result)
    else:
        lines = result.splitlines()
        assert lines[0] == "not equivalent", (lhs, rhs, result)
        witness = lines[1].removeprefix("counterexample: ")
        if witness == "@ (empty string)":
            witness = ""
        left = invoke("match", lhs, witness)
        right = invoke("match", rhs, witness)
        assert left != right, (lhs, rhs, witness, left, right)

for lhs, rhs, alphabet in [("aaaa", "aaab", "ab"), ("ab*ac", "ab*ad", "abcd")]:
    lines = invoke("equivalent", lhs, rhs).splitlines()
    witness = lines[1].removeprefix("counterexample: ")
    for size in range(len(witness)):
        for letters in itertools.product(alphabet, repeat=size):
            word = "".join(letters)
            assert invoke("match", lhs, word) == invoke("match", rhs, word)

expect(("equivalent", "a*b", "ab*"), "not equivalent\ncounterexample: b")

rng = random.Random(19464)
base = [("zero",), ("epsilon",), ("literal", "a"), ("literal", "b")]


def generate(depth):
    if depth == 0 or rng.randrange(4) == 0:
        return rng.choice(base)
    operator = rng.choice(["union", "concat", "star"])
    if operator == "star":
        return (operator, generate(depth - 1))
    return (operator, generate(depth - 1), generate(depth - 1))


expressions = set(base)
while len(expressions) < 80:
    expressions.add(generate(3))
words = ["".join(w) for length in range(4) for w in itertools.product("ab", repeat=length)]
words += ["c", "ac", "🙂"]
for expression in sorted(expressions, key=repr):
    regex = render(expression)
    expected = language(expression, 3)
    normalized = invoke("normalize", regex)
    expect(("normalize", normalized), normalized)
    expect(("match-many", regex, *words), "\n".join(str(word in expected).lower() for word in words))
    for word in words:
        accepted = str(word in expected).lower()
        expect(("match", regex, word), accepted)
        expect(("match", normalized, word), accepted)

trace = invoke("trace", "(a|b)*abb", "aabb")
assert trace.endswith("nullable: true"), trace
assert trace.count("  d/") == 4, trace
print(f"{checks} checks passed, including 80 generated expressions against finite-language enumeration")
