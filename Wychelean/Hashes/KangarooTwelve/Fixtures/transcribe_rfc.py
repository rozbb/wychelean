from pathlib import Path
import re
import argparse
parser=argparse.ArgumentParser(description="Transcribe all 67 vectors from https://www.rfc-editor.org/rfc/rfc9861.txt")
parser.add_argument('--rfc', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args=parser.parse_args()
text=args.rfc.read_text()
cases=[]
def size(s):
    parts=s.split('**')
    return int(parts[0])**int(parts[1]) if len(parts)==2 else int(s)
def material(s):
    s=s.removeprefix('M=').removeprefix('C=')
    if s=='`00`^0': return ('pattern',0)
    if s.startswith('ptn('): return ('pattern',size(s[4:-7]))
    assert re.fullmatch(r'`FF(?: FF)*`',s),s
    return ('ff',len(s[1:-1].split()))
for m in re.finditer(r'^     (TurboSHAKE128|TurboSHAKE256|KT128|KT256)\((.*?)\)(?:, last (\d+) bytes)?:\n\s*`([0-9A-F \n]+)`',text,re.M):
    fn,parameters,tail,hexout=m.groups()
    a,b,out=parameters.split(', ')
    mode,n=material(a); out=int(out); expected=''.join(hexout.split()).lower()
    if fn.startswith('KT'): cmode,cn=material(b); assert cmode=='pattern'; domain=0
    else: cn=0;domain=int(b[3:-1],16)
    offset=out-int(tail) if tail else 0
    assert len(expected)//2==out-offset
    cases.append((fn,mode,n,cn,domain,out,offset,expected))
assert len(cases)==67,len(cases)
lines=['-- Expected outputs transcribed from RFC 9861 §5, https://www.rfc-editor.org/rfc/rfc9861.html#section-5', 'def rfcCases : List XofVector := [']
for i,(fn,mode,n,cn,dom,out,off,expected) in enumerate(cases):
    lines.append(f'  ⟨"RFC 9861 {fn} case {i+1}", .{fn}, {str(mode=="ff").lower()}, {n}, {cn}, {dom}, {out}, {off}, "{expected}"⟩'+(',' if i<len(cases)-1 else ''))
lines+= [']']
args.output.write_text('\n'.join(lines)+'\n')
print(len(cases),'RFC cases transcribed')
