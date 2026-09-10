from pathlib import Path
import sys
import argparse
parser=argparse.ArgumentParser(description="Generate extra boundary vectors from the pinned XKCP/K12 Python reference (CC0).")
parser.add_argument('--reference-directory', type=Path, required=True,
    help='Python directory from XKCP/K12 commit f95b0b73e29fe75fe99fbbb24c8000d9fcf0b40e')
parser.add_argument('--output', type=Path, required=True)
args=parser.parse_args()
sys.path.insert(0,str(args.reference_directory))
from KangarooTwelve import KT128,KT256,length_encode
from TurboSHAKE import TurboSHAKE128,TurboSHAKE256

def pattern(n): return bytes(i%251 for i in range(n))
cases=[]
for strength,kt,ts,r in [(128,KT128,TurboSHAKE128,168),(256,KT256,TurboSHAKE256,136)]:
    for total in [8191,8192,8193,16383,16384,16385]:
        for c in [0,255,256]:
            m=total-c-len(length_encode(c));out=strength//4+1
            expected=kt(pattern(m),pattern(c),out).hex()
            cases.append((f'KT{strength} encoded S={total}, C={c}',f'KT{strength}',m,c,0,out,expected))
    for m in [0,16384]:
        expected=kt(pattern(m),pattern(3),0).hex()
        cases.append((f'KT{strength} zero output M={m}',f'KT{strength}',m,3,0,0,expected))
    for m in [r-1,r,r+1,2*r-1,2*r,2*r+1]:
        for domain in [1,127]:
            expected=ts(pattern(m),domain,r+1).hex()
            cases.append((f'TurboSHAKE{strength} M={m}, D={domain}',f'TurboSHAKE{strength}',m,0,domain,r+1,expected))
    for out in [0,1,r-1,r,r+1]:
        cases.append((f'TurboSHAKE{strength} output={out}',f'TurboSHAKE{strength}',0,0,31,out,ts(b'',31,out).hex()))
lines=['''/-- Additional boundary cases generated with the pinned XKCP/K12 Python reference (CC0).
https://github.com/XKCP/K12/tree/f95b0b73e29fe75fe99fbbb24c8000d9fcf0b40e/Python
These are generated reference outputs, not published RFC vectors. -/
def boundaryCases : List XofVector := [''']
lines+=['  ⟨"%s", .%s, false, %d, %d, %d, %d, 0, "%s"⟩'%c+(',' if i<len(cases)-1 else '') for i,c in enumerate(cases)]
lines+= [']']
args.output.write_text('\n'.join(lines)+'\n')
print(len(cases),'reference boundary cases')
