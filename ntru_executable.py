
from fractions import Fraction as frac
from math import gcd
import math
from operator import mod

def egcd(a, b):
    x, y, u, v = 0, 1, 1, 0
    while a != 0:
        q, r = b // a, b % a
        m, n = x - u*q, y - v*q
        b, a, x, y, u, v = a, r, u, v, m, n
    return b, x, y

def modinv(a, m):
    g, x, _ = egcd(a, m)
    return None if g != 1 else x % m

def fracMod(f, m):
    if not isinstance(f, frac):
        f = frac(f, 1)
    g, _, _ = egcd(f.denominator, m)
    if g != 1:
        raise ValueError(f"No modular inverse for denominator {f.denominator} modulo {m}")
    return (modinv(f.denominator, m) * f.numerator) % m

def trim(seq):
    seq = list(seq)
    if not seq:
        return [0]
    for i in range(len(seq)-1, -1, -1):
        if seq[i] != 0:
            return seq[:i+1]
    return [0]

def resize(c1, c2):
    c1, c2 = list(c1), list(c2)
    if len(c1) < len(c2): c1 += [0]*(len(c2)-len(c1))
    if len(c2) < len(c1): c2 += [0]*(len(c1)-len(c2))
    return c1, c2

def addPoly(c1, c2):
    c1, c2 = resize(c1, c2)
    return trim([a+b for a, b in zip(c1,c2)])

def subPoly(c1, c2):
    c1, c2 = resize(c1, c2)
    return trim([a-b for a, b in zip(c1,c2)])

def multPoly(c1, c2):
    c1, c2 = trim(c1), trim(c2)
    out = [0]*(len(c1)+len(c2)-1)
    for i, a in enumerate(c1):
        for j, b in enumerate(c2):
            out[i+j] += a*b
    return trim(out)

def divPoly(N, D):
    N = list(map(frac, trim(N)))
    D = list(map(frac, trim(D)))
    if D == [0]:
        raise ZeroDivisionError("Polynomial division by zero")
    degN, degD = len(N)-1, len(D)-1
    if degN < degD:
        return [[0], trim(N)]
    q = [frac(0,1)]*(degN-degD+1)
    while degN >= degD and N != [0]:
        shifted = [frac(0,1)]*(degN-degD) + list(D)
        coeff = N[degN]/shifted[-1]
        q[degN-degD] = coeff
        subtractor = [x*coeff for x in shifted]
        N = subPoly(N, subtractor)
        degN = len(N)-1
    return [trim(q), trim(N)]

def modPoly(c, k):
    if k == 0:
        raise ValueError("Modulus cannot be zero")
    return [fracMod(x, k) for x in c]

def cenPoly(c, q):
    c = modPoly(c, q)
    half = q/2.0
    return [x - q if x > half else x for x in c]

def extEuclidPoly(a, b):
    switch = False
    a, b = trim(a), trim(b)
    if len(a) < len(b):
        a, b = b, a
        switch = True
    r0, r1 = a, b
    s0, s1 = [1], [0]
    t0, t1 = [0], [1]
    while r1 != [0]:
        q, r2 = divPoly(r0, r1)
        r0, r1 = r1, r2
        s0, s1 = s1, subPoly(s0, multPoly(q, s1))
        t0, t1 = t1, subPoly(t0, multPoly(q, t1))
    scale = r0[-1]
    gcd_val = [x/scale for x in r0]
    s_out = [x/scale for x in s0]
    t_out = [x/scale for x in t0]
    return [gcd_val, t_out, s_out] if switch else [gcd_val, s_out, t_out]

def isTernary(f, alpha, beta):
    return all(x in (-1,0,1) for x in f) and f.count(1) == alpha and f.count(-1) == beta

class Ntru:
    def __init__(self, N_new, p_new, q_new):
        self.N, self.p, self.q = N_new, p_new, q_new
        self.D = [-1] + [0]*(self.N-1) + [1]
        self.f = self.g = self.h = self.f_p = self.f_q = None
        self.d = None
    def genPublicKey(self, f_new, g_new, d_new):
        self.f, self.g, self.d = f_new, g_new, d_new
        _, s_f, _ = extEuclidPoly(self.f, self.D)
        self.f_p = modPoly(s_f, self.p)
        self.f_q = modPoly(s_f, self.q)
        self.h = self.reModulo(multPoly(self.f_q, self.g), self.D, self.q)
        if not self.runTests():
            raise ValueError("Invalid NTRU parameters")
    def getPublicKey(self):
        return self.h
    def setPublicKey(self, public_key):
        self.h = public_key
    def encrypt(self, message, randPol):
        if self.h is None:
            raise ValueError("Public key is not set")
        e_tilda = addPoly(multPoly(multPoly([self.p], randPol), self.h), message)
        return self.reModulo(e_tilda, self.D, self.q)
    def decrypt(self, encryptedMessage):
        tmp = self.reModulo(multPoly(self.f, encryptedMessage), self.D, self.q)
        centered = cenPoly(tmp, self.q)
        m1 = multPoly(self.f_p, centered)
        return trim(self.reModulo(m1, self.D, self.p))
    def reModulo(self, num, div, modby):
        _, remain = divPoly(num, div)
        return modPoly(remain, modby)
    def isPrimeN(self):
        if self.N <= 1: return False
        if self.N == 2: return True
        if self.N % 2 == 0: return False
        return all(self.N % i != 0 for i in range(3, int(math.sqrt(self.N))+1, 2))
    def runTests(self):
        if not self.isPrimeN(): print("Error: N is not prime"); return False
        if gcd(self.N, self.p) != 1: print("Error gcd N p"); return False
        if gcd(self.N, self.q) != 1: print("Error gcd N q"); return False
        if self.q <= (6*self.d + 1)*self.p: print("Error q small"); return False
        if not isTernary(self.f, self.d+1, self.d): print("Error f ternary"); return False
        if not isTernary(self.g, self.d, self.d): print("Error g ternary"); return False
        return True

def string_to_ascii(msg):
    return [ord(ch) for ch in msg]

def ascii_to_string(vals):
    return ''.join(chr(int(v)) for v in vals if 0 <= int(v) <= 1114111)

def main():
    print("Bob will generate his public key using parameters")
    print("N = 97, p = 125, q = 491531")
    bob = Ntru(97, 125, 491531)
    f = [1, 1, -1, 0, -1, 1]
    g = [-1, 0, 1, 1, 0, 0, -1]
    d = 2
    bob.genPublicKey(f, g, d)
    pub_key = bob.getPublicKey()
    print("Public Key Generated by Bob:", pub_key)
    alice = Ntru(97,125,491531)
    alice.setPublicKey(pub_key)
    msg_text = "HELLO"
    msg = string_to_ascii(msg_text)
    rand_pol = [-1, -1, 1, 1]
    encrypted_msg = alice.encrypt(msg, rand_pol)
    decrypted_msg = bob.decrypt(encrypted_msg)
    print("Original Text:", msg_text)
    print("ASCII:", msg)
    print("Encrypted Message:", encrypted_msg)
    print("Decrypted Message:", decrypted_msg)
    print("Recovered Text:", ascii_to_string(decrypted_msg))

if __name__ == "__main__":
    main()
