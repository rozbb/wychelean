"""Offline derivation of additional Keccak-p cases from FIPS 202 Algorithms 1–7.
Uses individual bits, independently of the Lean lane-based implementation.
XKCP inputs: https://github.com/XKCP/XKCP/tree/eb5244d6b95fb1c434b211bac293093e18aa8fd1/tests/TestVectors
FIPS 202: https://doi.org/10.6028/NIST.FIPS.202
Published XKCP traces are transcribed separately; they are never generated here.
"""
from pathlib import Path
import re

def permutation(bits, ell, nr):
    w = 1 << ell
    a = [[[bits[w*(5*y+x)+z] for z in range(w)] for y in range(5)] for x in range(5)]
    for ir in range(12+2*ell-nr,12+2*ell):
        c = [[sum(a[x][y][z] for y in range(5)) % 2 for z in range(w)] for x in range(5)]
        a = [[[a[x][y][z] ^ c[(x-1)%5][z] ^ c[(x+1)%5][(z-1)%w] for z in range(w)] for y in range(5)] for x in range(5)]
        rho = [[row[:] for row in col] for col in a]
        x,y=1,0
        for t in range(24):
            rho[x][y]=[a[x][y][(z-(t+1)*(t+2)//2)%w] for z in range(w)]
            x,y=y,(2*x+3*y)%5
        a = [[rho[(x+3*y)%5][x][:] for y in range(5)] for x in range(5)]
        a = [[[a[x][y][z] ^ ((1 ^ a[(x+1)%5][y][z]) & a[(x+2)%5][y][z]) for z in range(w)] for y in range(5)] for x in range(5)]
        for j in range(ell+1):
            r = [1,0,0,0,0,0,0,0]
            for _ in range((j+7*ir)%255):
                r = [0]+r
                for k in [0,4,5,6]: r[k] ^= r[8]
                r = r[:8]
            a[0][0][(1<<j)-1] ^= r[0]
    return [a[(i//w)%5][i//w//5][i%w] for i in range(25*w)]

def hex_bits(bits):
    return bytes(sum(bits[i+j] << j for j in range(min(8,len(bits)-i))) for i in range(0,len(bits),8)).hex()

def published_cases(root):
    cases=[]
    for ell in range(3,7):
        width=25*(1<<ell); rounds=12+2*ell
        text=(root/f'KeccakF-{width}-IntermediateValues.txt').read_text()
        text='\n'.join(line.rstrip() for line in text.splitlines())+'\n'
        states=[]
        for m in re.finditer(r'After iota:\n((?:[0-9A-F]+(?: [0-9A-F]+){4}\n){5})',text):
            words=m[1].split(); assert len(words)==25
            states.append(b''.join(int(x,16).to_bytes((1<<ell)//8,'little') for x in words).hex())
        assert len(states)==2*rounds
        for trace in range(2):
            input='00'*(width//8) if trace==0 else states[rounds-1]
            cases.append((f'XKCP {width} trace {trace+1} full',ell,rounds,input,states[(trace+1)*rounds-1]))
            if width==800:
                cases.append((f'XKCP 800 trace {trace+1} rounds 10–21',ell,12,states[trace*rounds+9],states[(trace+1)*rounds-1]))
    return cases

def generated_cases():
    cases=[]
    for ell in range(7):
        width=25*(1<<ell)
        for pattern in range(3):
            bits=[0 if pattern==0 else 1 if pattern==1 else (i*7+i//3)%2 for i in range(width)]
            for nr in sorted(set([0,1,12,12+2*ell,18+2*ell])):
                out=permutation(bits,ell,nr)
                cases.append((f'FIPS bit reference b={width} nr={nr} pattern={pattern}',ell,nr,hex_bits(bits),hex_bits(out)))
    return cases

def lean_cases(name,cases):
    return 'def '+name+' : List PermutationVector := [\n'+',\n'.join('  ⟨"%s", %d, %d, "%s", "%s"⟩'%c for c in cases)+'\n]\n'

def sponge(msg,ell,nr,r,d):
    p=msg+[1]+[0]*((-len(msg)-2)%r)+[1]
    b=25*(1<<ell);s=[0]*b
    for i in range(0,len(p),r):
        s=permutation([x^(p[i+j] if j<r else 0) for j,x in enumerate(s)],ell,nr)
    output=[]
    while len(output)<d:
        output+=s[:r]
        if len(output)<d:s=permutation(s,ell,nr)
    return output[:d]

def sponge_cases():
    cases=[]
    for ell in range(7):
        b=25*(1<<ell)
        for r in [1,b//2,b-1]:
            for n in sorted(set([0,r-1,r,r+1])):
                bits=[(i*7+i//3)%2 for i in range(n)]
                nr=12+2*ell;d=r+1
                cases.append(f'  ⟨{ell}, {nr}, {r}, {n}, "{hex_bits(bits)}", {d}, "{hex_bits(sponge(bits,ell,nr,r,d))}"⟩')
    return "def spongeVectors : List SpongeVector := [\n"+",\n".join(cases)+"\n]\n"

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--xkcp-directory', type=Path, required=True,
        help='Directory containing pinned XKCP KeccakF-{200,400,800,1600}-IntermediateValues.txt')
    parser.add_argument('--output', type=Path, required=True, help='Output Lean fixture declarations')
    args=parser.parse_args()
    pub=published_cases(args.xkcp_directory)
    gen=generated_cases()
    # Cross-check independent bit implementation with all published traces, including p[800,12].
    for name,ell,nr,inp,out in pub:
        raw=bytes.fromhex(inp); bits=[(raw[i//8]>>(i%8))&1 for i in range(25*(1<<ell))]
        assert hex_bits(permutation(bits,ell,nr))==out,name
    args.output.write_text(lean_cases('published',pub)+'\n'+lean_cases('generated',gen)+'\n'+sponge_cases())
    print(len(pub),'published,',len(gen),'independently generated cases')
