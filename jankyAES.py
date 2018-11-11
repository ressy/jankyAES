#!/usr/bin/env python3

"""
A shoddy AES-128-ECB implementation, created by naively following NIST FIPS 197
step-by-step in pure Python 3.

https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf
"""

m      = 0x11b # The magical irreducible polynomial for byte polynomials of bits in GF(2^8)
MW     = [0x03, 0x01, 0x01, 0x02] # The equivalent for the word polynomials of bytes
INV_MW = [0x0b, 0x0d, 0x09, 0x0e] # equivalent inverse
A      = 0x63 # The value to add for the affine transform for the Rijndael S-box
# I started writing things using Nk and Nb but eventually gave up and just
# started putting "4" all over the place.  Oh well.  It works for 128-bit block
# at least.
Nk = 4 # key length, in bytes
Nb = 4 # block size, in bytes
Nr = 10 # number of rounds

#### Underlying math in the magical wraparound land of GF(2^8)

# The simplest case of polynomial multiplication defined in GF(2^8):
# multiplying by x just shifts the bits left, but with an extra XOR to wrap
# around and keep the value below 2^8.
def xtime(b, n):
    while n >= 1:
        b = b << 1
        if (b > 0xff):
            b = b ^ m
        n -= 1
    return(b)

# General polynomial multiplication defined in GF(2^8).  For each bit of b2,
# multiply b1 by x the appropriate number of times and "add" (XOR) it to the
# total.  the special XOR in xtime ensures we always get a value < 0x100 back.
def gf_mult(b1, b2):
    b = 0
    for i in range(8):
        if (2**i & b2) > 0:
            b = b ^ xtime(b1, i)
    return(b)

# multiplicative inverse in GF(2^8).
# I think this is the most awful possible way to do this.
def gf_inv(b):
    if (b == 0):
        return(0)
    for b2 in range(1, 0x100):
        if (gf_mult(b, b2) == 1):
            return(b2)
    raise(Exception)

#### The Rijndael S Box and its inverse

# Give the i'th bit of the given byte, mod 8.
bi = lambda b, i: 0 + b & 2**(i%8) > 0

def s_box_sub(b_in):
    b = gf_inv(b_in) # Find the inverse of the input byte
    b_out = 0
    # For each bit position of the output byte, mix-n-match the input bits and
    # the affine transform bit, and place it in b_out at the right position.
    for i in range(8):
        newbit = bi(b, i) ^ bi(b, i+4) ^ bi(b, i+5) ^ bi(b, i+6) ^ bi(b, i+7) ^ bi(A, i)
        b_out = b_out ^ (newbit << i)
    return(b_out)

# Make a list of all possible S Box values for each possible byte.  The index
# in the list is in the input byte, and the value the output byte.
def build_s_box():
    return([s_box_sub(i) for i in range(0x100)])

# Make a list of all possible inverse S Box values for each possible byte.
def build_inv_s_box(s_box):
    return([s_box.index(i) for i in range(0x100)])

S_BOX = build_s_box()
INV_S_BOX = build_inv_s_box(S_BOX)

#### Cipher functions

# Substitute each byte in the given state with its S Box equivalent.  Pass in
# an inverse S box for the inverse substitution.
def sub_bytes(state, s_box):
    return([s_box[b] for b in state])

# Shift each row of the state by its row index.  fwd=False will inverse-shift.
def shift_rows(state, fwd=True):
    shift = lambda i: (i + (fwd*2-1)*(i%4)*4)%len(state)
    return([state[shift(i)]for i in range(len(state))])

# Mix a single column with the magical polynomial.
# FIPS 197 didn't have an explicit MixColumn example, but Wikipedia does:
# https://en.wikipedia.org/wiki/Rijndael_MixColumns
def mix_column(c, mw):
    # For byte of output
    c_out = [0]*4
    for i in range(4):
        # For byte of mw
        c_out[i] = 0
        for j in range(4):
            # Multiple mw and c element-wise, using the GF magic math
            k = (j-i-1)%4 # wraparound index in mw
            prod = gf_mult(mw[k], c[j]) # "multipy"
            c_out[i] = c_out[i] ^ prod # "add"
    return(c_out)

# Independently perform a matrix multiplication of each column with a matrix
# formed with cyclically-shifted versions of mw.
def mix_columns(state, mw):
    state_out = [0]*Nb*Nk
    for i in range(4):
        state_out[i*4:i*4+4] = mix_column(state[i*4:i*4+4], mw)
    return(state_out)

# Independently add in a round key to each byte in the state.
def add_round_key(state, rk):
    # rk is a list of lists.  we need it lined up with the state.
    rk_long = [0]*len(state)
    for i in range(len(rk_long)):
        rk_long[i] = rk[i//4][i%4]
    return([state[i] ^ rk_long[i] for i in range(len(state))])

# It's just the same sub_bytes operation as before.
sub_word = sub_bytes

rot_word = lambda w: w[1:] + [w[0]]

# "Round constant" (?) I don't really get this part.
rcon = lambda i: [xtime(1, i-1)] + [0]*(Nk-1)

word_xor = lambda w1, w2: [b1 ^ b2 for b1, b2 in zip(w1, w2)]

# "The AES algorithm takes the Cipher Key, K, and performs a Key Expansion
# routine to generate a key schedule. The Key Expansion generates a total of Nb
# (Nr + 1) words: the algorithm requires an initial set of Nb words, and each
# of the Nr rounds requires Nb words of key data. The resulting key schedule
# consists of a linear array of 4-byte words, denoted [wi ], with i in the
# range 0 £ i < Nb(Nr + 1)."
#
# Hey look, their pseudo code in Figure 11 pretty much just works as Python
# as-is.
def key_expansion(key, s_box):
    # first, fill in the words for the input key.
    w = [[] for i in range(Nb*(Nr+1))]
    for i in range(Nk):
        w[i] = key[i*Nk:(i+1)*Nk]
    # Next, fill in the rest of the words.
    for i in range(Nk, Nb*(Nr+1)):
        temp = w[i-1]
        if i % Nk is 0:
            r = rcon(i//Nk)
            after_rot = rot_word(temp)
            after_sub = sub_word(after_rot, s_box)
            temp = word_xor(after_sub, r)
        elif Nk > 6 and i % Nk is 4:
            temp = sub_word(temp, s_box)
        w[i]  = word_xor(w[i - Nk], temp)
    return(w)

# cipher a single chunk.
def cipher(in_b, key):
    w = key_expansion(key, S_BOX)
    state = in_b
    rk = w[0:Nk]
    state = add_round_key(state, rk)
    for rnd in range(1, Nr):
        state = sub_bytes(state, S_BOX)
        state = shift_rows(state)
        state = mix_columns(state, MW)
        rk = w[(rnd*Nb):(rnd*Nb)+Nk]
        state = add_round_key(state, rk)
    state = sub_bytes(state, S_BOX)
    state = shift_rows(state)
    rk = w[Nb*Nr:Nb*Nr+Nk]
    state = add_round_key(state, rk) 
    return(state)

# inverse-cipher a single chunk.
def inv_cipher(in_b, key):
    w = key_expansion(key, S_BOX)
    state = in_b
    rk = w[Nb*Nr:Nb*Nr+Nk]
    state = add_round_key(state, rk)
    for rnd in range(Nr-1, 0, -1):
        state = shift_rows(state, fwd=False)
        state = sub_bytes(state, INV_S_BOX)
        rk = w[(rnd*Nb):(rnd*Nb)+Nk]
        state = add_round_key(state, rk)
        state = mix_columns(state, INV_MW)
    state = shift_rows(state, fwd=False)
    state = sub_bytes(state, INV_S_BOX)
    rk = w[0:Nk]
    state = add_round_key(state, rk)
    return(state)

#### Helpers

def decrypt(data, key):
    key = list(key)
    data_out = bytearray()
    for i in range(0, len(data), Nk*Nb):
        block = list(data[i:i+Nk*Nb])
        out = inv_cipher(block, key)
        data_out.extend(out)
    return(data_out)

#### Test Cases

# See FIPS 197 Appendix B
def run_tests():
    data      = [0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34]
    out_known = [0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb, 0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32]
    key       = [0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c]
    out = cipher(data, key)
    data_back = inv_cipher(out, key)
    if out_known != out:
        raise(RuntimeError("Test cipher failed."))
    if data != data_back:
        raise(RuntimeError("Test inverse cipher failed."))

run_tests()
