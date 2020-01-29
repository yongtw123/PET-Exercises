#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 01
#
# Basics of Petlib, encryption, signatures and
# an end-to-end encryption system.
#
# Run the tests through:
# $ py.test-2.7 -v Lab01Tests.py 

###########################
# Group Members: TODO
###########################


#####################################################
# TASK 1 -- Ensure petlib is installed on the System
#           and also pytest. Ensure the Lab Code can 
#           be imported.

import petlib

#####################################################
# TASK 2 -- Symmetric encryption using AES-GCM 
#           (Galois Counter Mode)
#
# Implement a encryption and decryption function
# that simply performs AES_GCM symmetric encryption
# and decryption using the functions in petlib.cipher.

from os import urandom
from petlib.cipher import Cipher

def encrypt_message(K, message):
    """ Encrypt a message under a key K """

    plaintext = message.encode("utf8")
    iv = urandom(len(K))
    aes = Cipher("aes-128-gcm")
    ciphertext, tag = aes.quick_gcm_enc(K, iv, plaintext)

    return (iv, ciphertext, tag)

def decrypt_message(K, iv, ciphertext, tag):
    """ Decrypt a cipher text under a key K 

        In case the decryption fails, throw an exception.
    """
    aes = Cipher("aes-128-gcm")
    # Throws exception on decryption failure
    plain = aes.quick_gcm_dec(K, iv, ciphertext, tag)

    return plain.encode("utf8")

#####################################################
# TASK 3 -- Understand Elliptic Curve Arithmetic
#           - Test if a point is on a curve.
#           - Implement Point addition.
#           - Implement Point doubling.
#           - Implement Scalar multiplication (double & add).
#           - Implement Scalar multiplication (Montgomery ladder).
#
# MUST NOT USE ANY OF THE petlib.ec FUNCIONS. Only petlib.bn!

from petlib.bn import Bn


def is_point_on_curve(a, b, p, x, y):
    """
    Check that a point (x, y) is on the curve defined by a,b and prime p.
    Reminder: an Elliptic Curve on a prime field p is defined as:

              y^2 = x^3 + ax + b (mod p)
                  (Weierstrass form)

    Return True if point (x,y) is on curve, otherwise False.
    By convention a (None, None) point represents "infinity".
    """
    assert isinstance(a, Bn)
    assert isinstance(b, Bn)
    assert isinstance(p, Bn) and p > 0
    assert (isinstance(x, Bn) and isinstance(y, Bn)) \
           or (x == None and y == None)

    #if x == None and y == None:
    if x is None and y is None:
        return True

    lhs = (y * y) % p
    rhs = (x*x*x + a*x + b) % p
    on_curve = (lhs == rhs)

    return on_curve


def point_add(a, b, p, x0, y0, x1, y1):
    """Define the "addition" operation for 2 EC Points.

    Reminder: (xr, yr) = (xq, yq) + (xp, yp)
    is defined as:
        lam = (yq - yp) * (xq - xp)^-1 (mod p)
        xr  = lam^2 - xp - xq (mod p)
        yr  = lam * (xp - xr) - yp (mod p)

    Return the point resulting from the addition. Raises an Exception if the points are equal.
    """
    xr, yr = None, None

    if not all([x0, y0, x1, y1]):
        # Either is origin; inf is "(0,0)"
        xr = x0 or x1
        yr = y0 or y1
    elif (x0 == x1 and y0 == y1):
        # Point doubling
        #xr, yr = point_double(a, b, p, x0, y0)
        # NOTE: asked to raise exact exception
        raise Exception("EC Points must not be equal")
    elif (y0 + y1) % p == Bn(0):
        # Negation, checking y coord, return origin
        pass
    else:
        inv = (x1 - x0).mod_inverse(p)
        lam = ((y1 - y0) * inv) % p
        xr = (lam**2 - x0 - x1) % p
        yr = (lam * (x0 - xr) - y0) % p
    
    return (xr, yr)

def point_double(a, b, p, x, y):
    """Define "doubling" an EC point.
     A special case, when a point needs to be added to itself.

     Reminder:
        lam = (3 * xp ^ 2 + a) * (2 * yp) ^ -1 (mod p)
        xr  = lam ^ 2 - 2 * xp
        yr  = lam * (xp - xr) - yp (mod p)

    Returns the point representing the double of the input (x, y).
    """  

    xr, yr = None, None

    if not all([x, y]):
        # Is origin; inf is "(0,0)"
        pass
    else:
        inv = (2 * y).mod_inverse(p)
        lam = ((3 * (x ** 2) + a) * inv) % p
        xr = (lam**2 - 2 * x) % p
        yr = (lam * (x - xr) - y) % p

    return xr, yr

def point_scalar_multiplication_double_and_add(a, b, p, x, y, scalar):
    """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        Q = infinity
        for i = 0 to num_bits(P)-1
            if bit i of r == 1 then
                Q = Q + P
            P = 2 * P
        return Q

    """
    Q = (None, None)
    P = (x, y)

    for i in range(scalar.num_bits()):
        if scalar.is_bit_set(i):
            # unpacking Q and P as one list
            Q = point_add(a, b, p, *Q+P)
        P = point_double(a, b, p, *P)

    return Q

def point_scalar_multiplication_montgomerry_ladder(a, b, p, x, y, scalar):
    """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        R0 = infinity
        R1 = P
        for i in num_bits(P)-1 to zero:
            if i = 0:
                R1 = R0 + R1
                R0 = 2R0
            else
                R0 = R0 + R1
                R1 = 2 R1
        return R0

    """
    R0 = (None, None)
    R1 = (x, y)

    for i in reversed(range(0,scalar.num_bits())):
        if not scalar.is_bit_set(i):
            # unpacking R0 and R1 as one list
            R1 = point_add(a, b, p, *(R0+R1))
            R0 = point_double(a, b, p, *R0)
        else:
            # unpacking R0 and R1 as one list
            R0 = point_add(a, b, p, *(R0+R1))
            R1 = point_double(a, b, p, *R1)

    return R0


#####################################################
# TASK 4 -- Standard ECDSA signatures
#
#          - Implement a key / param generation 
#          - Implement ECDSA signature using petlib.ecdsa
#          - Implement ECDSA signature verification 
#            using petlib.ecdsa

from hashlib import sha256
from petlib.ec import EcGroup
from petlib.ecdsa import do_ecdsa_sign, do_ecdsa_verify

def ecdsa_key_gen():
    """ Returns an EC group, a random private key for signing 
        and the corresponding public key for verification"""
    G = EcGroup()
    priv_sign = G.order().random()
    pub_verify = priv_sign * G.generator()
    return (G, priv_sign, pub_verify)


def ecdsa_sign(G, priv_sign, message):
    """ Sign the SHA256 digest of the message using ECDSA and return a signature """
    plaintext =  message.encode("utf8")

    sig = do_ecdsa_sign(G, priv_sign, sha256(plaintext).digest())

    return sig

def ecdsa_verify(G, pub_verify, message, sig):
    """ Verify the ECDSA signature on the message """
    plaintext =  message.encode("utf8")

    res = do_ecdsa_verify(G, pub_verify, sig, sha256(plaintext).digest())

    return res

#####################################################
# TASK 5 -- Diffie-Hellman Key Exchange and Derivation
#           - use Bob's public key to derive a shared key.
#           - Use Bob's public key to encrypt a message.
#           - Use Bob's private key to decrypt the message.
#
# NOTE: 

def dh_get_key():
    """ Generate a DH key pair """
    G = EcGroup()
    priv_dec = G.order().random()
    pub_enc = priv_dec * G.generator()
    return (G, priv_dec, pub_enc)


def dh_encrypt(pub, message, aliceSig = None):
    """ Assume you know the public key of someone else (Bob), 
    and wish to Encrypt a message for them.
        - Generate a fresh DH key for this message.
        - Derive a fresh shared key.
        - Use the shared key to AES_GCM encrypt the message.
        - Optionally: sign the message with Alice's key.
    """
    
    # pub is bob's pub key, alicesig is my private sig key,
    # which shuold be different from enc/dec keypair
    # for cryptographic sec reasons

    # priv is an integer, pub is an ec point
    alice_G, alice_priv, alice_pub = dh_get_key()

    # shared secret = my priv x bob's pub point
    shared_key = alice_priv * pub
    # hash ec pt to derive key
    shared_key = sha256(shared_key.export()).digest()

    # aes_gcm encrypt
    aes = Cipher("aes-256-gcm")
    iv = urandom(len(shared_key))
    ciphertext, tag = aes.quick_gcm_enc(shared_key, iv, message.encode("utf-8"))

    # sign message (assume using common curve)
    # hash ciphertext
    sig = do_ecdsa_sign(EcGroup(), aliceSig, sha256(ciphertext).digest()) if aliceSig else None

    # return alice_pub for dh_decrypt on bob side
    # (because bob needs alice's pub to gen shared secret)
    return (iv, ciphertext, tag, alice_pub, sig)

def dh_decrypt(priv, ciphertext, aliceVer = None):
    """ Decrypt a received message encrypted using your public key, 
    of which the private key is provided. Optionally verify 
    the message came from Alice using her verification key."""
    
    # ciphertext be (iv, ciphertext, tag, sender_pub, sig)
    # bob decrypting: check sig using alice's pub ver key,
    # then decrypt using shared key derived from priv (bob's private key)

    # check input parameter format
    if (not isinstance(ciphertext, tuple)) or (isinstance(ciphertext, tuple) and len(ciphertext) != 5):
        raise Exception("Expecting tuple (iv, ciphertext, tag, sender public key, signature).")
    iv, encmsg, tag, sender_pub, sig = ciphertext

    # verify signature
    if aliceVer:
        if not sig:
           raise Exception("Signature required before decyption.")
        elif not do_ecdsa_verify(EcGroup(), aliceVer, sig, sha256(encmsg).digest()):
           raise Exception("Signature verification failed.")
    
    # shared key = bob priv x alice's pub point
    shared_key = priv * sender_pub
    # hash
    shared_key = sha256(shared_key.export()).digest()

    # decrypt
    aes = Cipher("aes-256-gcm")
    plaintext = aes.quick_gcm_dec(shared_key, iv, encmsg, tag)

    return plaintext.encode("utf-8")

## NOTE: populate those (or more) tests
#  ensure they run using the "py.test filename" command.
#  What is your test coverage? Where is it missing cases?
#  $ py.test-2.7 --cov-report html --cov Lab01Code Lab01Code.py 

def test_encrypt():
    _, bob_priv, bob_pub = dh_get_key() # for enc/dec
    _, alice_sig, alice_ver = dh_get_key() # for sig/ver
    string = u"Tally ho!"

    enc = dh_encrypt(bob_pub, string)
    assert len(enc) == 5
    assert enc[4] is None
    assert len(enc[1]) == len(string)

    enc = dh_encrypt(bob_pub, string, alice_sig)
    assert len(enc) == 5
    assert enc[4] is not None
    assert len(enc[1]) == len(string)

def test_decrypt():
    _, bob_priv, bob_pub = dh_get_key() # for enc/dec
    _, alice_sig, alice_ver = dh_get_key() # for sig/ver
    string = u"You shall not pass!"

    enc = dh_encrypt(bob_pub, string, alice_sig) # bob encrypts sth to alice
    dec = dh_decrypt(bob_priv, enc, alice_ver)
    assert dec == string

    dec2 = dh_decrypt(bob_priv, enc) # allow decryption if signature verification is not requested
    assert dec2 == string

def test_fails():
    from pytest import raises

    _, bob_priv, bob_pub = dh_get_key() # for enc/dec
    _, alice_sig, alice_ver = dh_get_key() # for sig/ver
    string = u"The Doors of Durin, Lord of Moria. Speak, friend, and enter."

    iv, encmsg, tag, sender_pub, sig = dh_encrypt(bob_pub, string, alice_sig)

    # ciphertext not a tuple
    with raises(Exception) as excinfo:
        dh_decrypt(bob_priv, "aloha", alice_ver)
    assert 'Expecting tuple (iv, ciphertext, tag, sender public key, signature).' in str(excinfo.value)

    # ciphertext incomplete
    with raises(Exception) as excinfo:
        dh_decrypt(bob_priv, (iv, encmsg, tag), alice_ver)
    assert 'Expecting tuple (iv, ciphertext, tag, sender public key, signature).' in str(excinfo.value)

    # signature not supplied when needed
    with raises(Exception) as excinfo:
        dh_decrypt(bob_priv, (iv, encmsg, tag, sender_pub, None), alice_ver)
    assert 'Signature required before decyption.' in str(excinfo.value)

    # modified encrypted message
    with raises(Exception) as excinfo:
         dh_decrypt(bob_priv, (iv, urandom(len(encmsg)), tag, sender_pub, sig), alice_ver)
    assert 'Signature verification failed.' in str(excinfo.value)

    # wrong iv
    with raises(Exception) as excinfo:
         dh_decrypt(bob_priv, (urandom(len(iv)), encmsg, tag, sender_pub, sig), alice_ver)
    assert 'decryption failed' in str(excinfo.value)

    # wrong tag
    with raises(Exception) as excinfo:
         dh_decrypt(bob_priv, (iv, encmsg, urandom(len(tag)), sender_pub, sig), alice_ver)
    assert 'decryption failed' in str(excinfo.value)

    # NOTE: not going to test wrong shared secret since it is implied that both parties know 
    #       each other's public key, and DH is carried out successfully
    

#####################################################
# TASK 6 -- Time EC scalar multiplication
#             Open Task.
#           
#           - Time your implementations of scalar multiplication
#             (use time.clock() for measurements)for different 
#              scalar sizes)
#           - Print reports on timing dependencies on secrets.
#           - Fix one implementation to not leak information.

def time_scalar_mul():
    import time, pprint

    G = EcGroup()
    d = G.parameters()
    a, b, p = d["a"], d["b"], d["p"]
    g = G.generator()
    x, y = g.get_affine()
    scalars = G.order().hex()
    results = []

    for i in range(0, len(scalars), 3):
        r = Bn.from_hex(scalars[:i+1])
        start = time.clock()
        point_scalar_multiplication_double_and_add(a, b, p, x, y, r)
        elapsed = (time.clock() - start)
        results.append((r, elapsed))
    pp = pprint.PrettyPrinter(indent=2, width=160)
    pp.pprint(results)

    for i in range(0, len(scalars), 3):
        r = Bn.from_hex(scalars[:i+1])
        start = time.clock()
        point_scalar_multiplication_montgomerry_ladder(a, b, p, x, y, r)
        elapsed = (time.clock() - start)
        results.append((r, elapsed))
    pp = pprint.PrettyPrinter(indent=2, width=160)
    pp.pprint(results)
