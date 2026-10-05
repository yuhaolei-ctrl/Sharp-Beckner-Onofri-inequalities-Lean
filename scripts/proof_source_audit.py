"""Lexical proof-hole scan, supplementary to Lean's transitive axiom audit."""
import re


def code_only(source):
    output = []
    i = depth = 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            output.append('  ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            output.append('  ')
            i += 2
        elif depth:
            output.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            end = len(source) if end < 0 else end
            output.append(' ' * (end - i))
            i = end
        elif source[i] == '"':
            output.append(' ')
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    output.extend('  ')
                    i += 2
                elif source[i] == '"':
                    output.append(' ')
                    i += 1
                    break
                else:
                    output.append('\n' if source[i] == '\n' else ' ')
                    i += 1
        else:
            output.append(source[i])
            i += 1
    return ''.join(output)


def forbidden_hits(source):
    return [(source.count('\n', 0, match.start()) + 1, match.group())
            for match in re.finditer(r'\b(sorry|admit|sorryAx|native_decide|axiom)\b', code_only(source))]
