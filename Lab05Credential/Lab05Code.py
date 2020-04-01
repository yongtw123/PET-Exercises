#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 05
#
# Selective Disclosure (Anonymous) Credentials
#
# Run the tests through:
# $ py.test -v test_file_name.py

###########################
# Group Members: TODO
###########################

from petlib.ec import EcGroup
from petlib.bn import Bn

from hashlib import sha256
from binascii import hexlify

#####################################################
# Background, setup, key derivation and utility 
# functions.
# 

def credential_setup():
    """ Generates the parameters of the algebraic MAC scheme"""
    G = EcGroup()
    g = G.hash_to_point(b"g")
    h = G.hash_to_point(b"h")
    o = G.order()

    params = (G, g, h, o)
    return params

def credential_KeyGenIssuer(params):
    """ Generates keys and parameters for the credential issuer for 1 attribute"""
    _, g, h, o = params

    # Generate x0, x1 as the keys to the algebraic MAC scheme
    x0, x1 = o.random(), o.random()
    sk = [x0, x1]
    iparams = x1 * h 

    # Generate a pedersen commitment Cx0 to x0 with opening x0_bar
    x0_bar = o.random()
    Cx0 = x0 * g + x0_bar * h

    return (Cx0, iparams), (sk, x0_bar)

def credential_KeyGenUser(params):
    """ Generates keys and parameters for credential user """
    G, g, h, o = params
    priv = o.random()
    pub = priv * g # This is just an EC El-Gamal key
    return (priv, pub)

## This is our old friend "to_challenge" from Lab04 on Zero Knowledge

def to_challenge(elements):
    """ Generates a Bn challenge by hashing a number of EC points """
    Cstring = b",".join([hexlify(x.export()) for x in elements])
    Chash =  sha256(Cstring).digest()
    return Bn.from_binary(Chash)

#####################################################
# TASK 1 -- User Encrypts a secret value v and sends
#           and sends it to the issuer. This v will 
#           become the single attribute of the user.
#           Prove in ZK that the user knows v and the
#           private key of pub.

## IMPORTANT NOTE: The reference scheme for all the 
# techniques in this exercise are in section 
# "4.2 Keyed-verification credentials from MAC_GGM"
# pages 8-9 of https://eprint.iacr.org/2013/516.pdf

def credential_EncryptUserSecret(params, pub, priv):
    """ Encrypt a user defined random secret v under the public key of the user. 
        Prove knowledge of the secret v, the private key "priv" and correctness of 
        the encryption """
    G, g, h, o = params
    v = o.random()
    
    ## Encrypt v using Benaloh with randomness k
    k = o.random()
    ciphertext = k * g, k * pub + v * g
    a, b = ciphertext

    ## Prove knowledge of the encrypted v and priv in ZK
    #  NIZK{(v, k, priv): a = k * g and 
    #                     b = k * pub + v * g and 
    #                     pub = priv * g}

    # NOTE: Wap and Wbp share a common witness w[0] for secret k
    #       Wbp has a witness w[1] for secret v
    #       Wbpub has a witness w[2] for secret priv
    witnesses = [o.random() for _ in range(3)]
    Wap = witnesses[0] * g 
    Wbp = witnesses[0] * pub + witnesses[1] * g
    Wpubp = witnesses[2] * g
    c = to_challenge([g, pub, a, b, Wap, Wbp, Wpubp])

    rk = witnesses[0] - c * k
    rv = witnesses[1] - c * v
    rpriv = witnesses[2] - c * priv

    # Return the fresh v, the encryption of v and the proof.
    proof = (c, rk, rv, rpriv)
    return v, ciphertext, proof


def credential_VerifyUserSecret(params, pub, ciphertext, proof):
    """ Verify the ciphertext is a correct encryption and the 
        proof of knowledge of the secret key "priv" """
    G, g, h, o = params

    ## The cipher text and its proof of correctness
    a, b = ciphertext
    (c, rk, rv, rpriv) = proof

    # Verify knowledge of the encrypted k, v and priv
    Wap = c * a + rk * g
    Wbp = c * b + rk * pub + rv * g
    Wpubp = c * pub + rpriv * g

    cp = to_challenge([g, pub, a, b, Wap, Wbp, Wpubp])
    return cp == c


#####################################################
# TASK 2 -- The issuer issues an
#           algebraic MAC on v, along with a ZK proof
#           that the MAC is correctly formed. The user
#           decrypts and verifies the MAC.

## IMPRTANT NOTE: Study the section "Issuance" p.8 
#  of https://eprint.iacr.org/2013/516.pdf

def credential_Issuing(params, pub, ciphertext, issuer_params):
    """ A function used by the credential issuer to provide a MAC
        on a secret (encrypted) attribute v """

    G, g, h, o = params
    
    ## The public and private parameters of the issuer 
    (Cx0, iparams), (sk, x0_bar) = issuer_params
    X1 = iparams
    x0, x1 = sk

    # The ciphertext of the encrypted attribute v
    a, b = ciphertext

    # 1) Create a "u" as u = beta*g 
    # 2) Create a X1b as X1b == beta * X1 == (beta * x1) * h
    #     and x1b = (beta * x1) mod o 
    
    # TODO 1 & 2
    beta = o.random()
    u = beta * g
    X1b = beta * X1 # X1 is (x1 * h)
    x1b = (beta * x1) % o # for the other representaton of X1b

    # 3) The encrypted MAC is u, and an encrypted u_prime defined as 
    #    E( (beta*x0) * g + (x1 * beta * v) * g ) + E(0; r_prime)
    
    # TODO 3
    # NOTE: Aim to construct encryption of u' from ciphertext (a,b)
    #       Why? Because only b has info about secret v
    #       => utilize homomorphic property x1b * ciphertext
    #       => (x1b * a    , x1b * b)
    #       => (x1b * k * g, x1b * pub + x1b * v * g) 
    #          Right-hand side is close to what we want!
    #          Just add (beta * x0) * g or x0 * u!

    r_prime = o.random() # for homomorphic encryption
    # E(u'; k' = x1b*k) = (k'*g, k'*pub + u')
    # NOTE Add E(0; r')
    new_a = x1b * a + r_prime * g
    new_b = x1b * b + x0 * u + r_prime * pub

    ciphertext = new_a, new_b

    ## A large ZK proof that:
    #  NIZK{(x1, beta, x1b, r_prime, x0, x0_bar)
    #       X1  = x1 * h
    #       X1b = beta * X1
    #       X1b = x1b * h
    #       u   = beta * g
    #       new_a = r_prime * g + x1b * a
    #       new_b = r_prime * pub + x1b * b + x0 * u 
    #       Cx0 = x0 * g + x0_bar * h }

    ## TODO proof
    witnesses = [o.random() for _ in range(6)] # x1, beta, x1b, r', x0, x0_bar
    W_X1 = witnesses[0] * h
    W_X1bb = witnesses[1] * X1
    W_X1bx = witnesses[2] * h
    W_u = witnesses[1] * g
    W_a = witnesses[3] * g + witnesses[2] * a
    W_b = witnesses[3] * pub + witnesses[2] * b + witnesses[4] * u
    W_Cx0 = witnesses[4] * g + witnesses[5] * h
    c = to_challenge([g, h, pub, a, b, X1, X1b, new_a, new_b, Cx0,
                      W_X1, W_X1bb, W_X1bx, W_u, W_a, W_b, W_Cx0])

    rs = [
        witnesses[0] - c * x1,
        witnesses[1] - c * beta,
        witnesses[2] - c * x1b,
        witnesses[3] - c * r_prime,
        witnesses[4] - c * x0,
        witnesses[5] - c * x0_bar
    ]

    proof = (c, rs, X1b) # Where rs are multiple responses

    return u, ciphertext, proof

def credential_Verify_Issuing(params, issuer_pub_params, pub, u, Enc_v, Enc_u_prime, proof):
    """ User verifies that the proof associated with the issuance 
        of the credential is valid. """

    G, g, h, o = params

    ## The public parameters of the issuer.
    (Cx0, iparams) = issuer_pub_params
    X1 = iparams

    ## The ciphertext of the encrypted attribute v and the encrypted u_prime
    a, b = Enc_v
    new_a, new_b = Enc_u_prime
    
    ## The proof of correctness
    (c, rs, X1b) = proof

    c_prime = to_challenge([g, h, pub, a, b, X1, X1b, new_a, new_b, Cx0,
                    c * X1 + rs[0] * h,
                    c * X1b + rs[1] * X1,
                    c * X1b + rs[2] * h,
                    c * u + rs[1] * g,
                    c * new_a + rs[3] * g + rs[2] * a,
                    c * new_b + rs[3] * pub + rs[2] * b + rs[4] * u,
                    c * Cx0 + rs[4] * g + rs[5] * h
                    ])

    return c_prime == c

def credential_Decrypt(params, priv, u, Enc_u_prime):
    """ Decrypt the second part of the credential u_prime """

    G, g, h, o = params
    new_a, new_b = Enc_u_prime
    u_prime = new_b - priv * new_a
    return (u, u_prime)

#####################################################
# TASK 3 -- The user re-blinds the MAC and proves
#           its possession without revealing the secret
#           attribute.

## IMPORTANT NOTE: Study the section "Credential presentation"
#  p.9 of https://eprint.iacr.org/2013/516.pdf

def credential_show(params, issuer_pub_params, u, u_prime, v):
    """ The user blinds the credential (u, u_prime) and then
        proves its correct possession."""

    G, g, h, o = params
    
    ## The public parameters of the credential issuer
    (Cx0, iparams) = issuer_pub_params
    X1 = iparams

    # 1) First blind the credential (u, u_prime)
    #    using (alpha * u, alpha * u_prime) for a
    #    random alpha.
    
    # TODO 1
    alpha = o.random()
    u = alpha * u
    u_prime = alpha * u_prime

    # 2) Implement the "Show" protocol (p.9) for a single attribute v.
    #    Cv is a commitment to v and Cup is C_{u'} in the paper. 

    # TODO 2
    z1 = o.random()
    r = o.random()
    Cv = v * u + z1 * h
    Cup = u_prime + r * g

    tag = (u, Cv, Cup)

    # Proof or knowledge of the statement
    #
    # NIZK{(r, z1, v): 
    #           Cv = v *u + z1 * h and
    #           V  = r * (-g) + z1 * X1 }

    ## TODO proof
    witnesses = [o.random() for _ in range(3)]
    W1 = witnesses[2] * u + witnesses[1] * h
    W2 = witnesses[0] * g + witnesses[1] * X1
    c = to_challenge([g, h, Cx0, X1, Cv, Cup, W1, W2])

    rr = witnesses[0] + c * r
    rz1 = witnesses[1] - c * z1
    rv = witnesses[2] - c * v

    proof = (c, rr, rz1, rv)
    return tag, proof

def credential_show_verify(params, issuer_params, tag, proof):
    """ Take a blinded tag and a proof of correct credential showing and verify it """

    G, g, h, o = params

    ## Public and private issuer parameters
    (Cx0, iparams), (sk, x0_bar) = issuer_params
    x0, x1 = sk
    X1 = iparams

    # Verify proof of correct credential showing
    (c, rr, rz1, rv) = proof
    (u, Cv, Cup) = tag

    ## TODO
    V = x1 * Cv + x0 * u - Cup
    c_prime = to_challenge([g, h, Cx0, X1, Cv, Cup,
        c * Cv + rv * u + rz1 * h,
        c * V + rr * g + rz1 * X1])

    return c == c_prime

#####################################################
# TASK 4 -- Modify the standard Show / ShowVerify process
#           to link the credential show to a long term 
#           pseudonym for a service. The pseudonyms should 
#           be unlikable between services.

def credential_show_pseudonym(params, issuer_pub_params, u, u_prime, v, service_name):
    """ From a credential (u, u_prime) generate a pseudonym H(service_name)^v 
        and prove you hold a valid credential with attribute v """

    G, g, h, o = params

    ## Public issuer parameters    
    (Cx0, iparams) = issuer_pub_params
    X1 = iparams

    ## A stable pseudonym associated with the service 
    N = G.hash_to_point(service_name)
    pseudonym = v * N

    ## TODO (use code from above and modify as necessary!)
    # 1) First blind the credential (u, u_prime)
    #    using (alpha * u, alpha * u_prime) for a
    #    random alpha.
    
    alpha = o.random()
    u = alpha * u
    u_prime = alpha * u_prime

    # 2) Implement the "Show" protocol (p.9) for a single attribute v.
    #    Cv is a commitment to v and Cup is C_{u'} in the paper. 

    z1 = o.random()
    r = o.random()
    Cv = v * u + z1 * h
    Cup = u_prime + r * g

    tag = (u, Cv, Cup)

    # Proof or knowledge of the statement
    #
    # NIZK{(r, z1, v): 
    #           Cv = v *u + z1 * h and
    #           V  = r * (-g) + z1 * X1
    #           pseudonym = v * N }

    ## TODO proof
    witnesses = [o.random() for _ in range(3)]
    W1 = witnesses[2] * u + witnesses[1] * h
    W2 = witnesses[0] * g + witnesses[1] * X1
    W3 = witnesses[2] * N
    c = to_challenge([g, h, Cx0, X1, Cv, Cup, W1, W2, W3])

    rr = witnesses[0] + c * r
    rz1 = witnesses[1] - c * z1
    rv = witnesses[2] - c * v

    proof = (c, rr, rz1, rv)
    return pseudonym, tag, proof

def credential_show_verify_pseudonym(params, issuer_params, pseudonym, tag, proof, service_name):
    """ Verify a pseudonym H(service_name)^v is generated by the holder of the 
        a valid credential with attribute v """

    G, g, h, o = params

    ## The public and private issuer parameters
    (Cx0, iparams), (sk, x0_bar) = issuer_params
    x0, x1 = sk
    X1 = iparams

    ## The EC point corresponding to the service
    N = G.hash_to_point(service_name)

    ## Verify the correct Show protocol and the correctness of the pseudonym

    # TODO (use code from above and modify as necessary!)
    # Verify proof of correct credential showing
    (c, rr, rz1, rv) = proof
    (u, Cv, Cup) = tag

    V = x1 * Cv + x0 * u - Cup
    c_prime = to_challenge([g, h, Cx0, X1, Cv, Cup,
        c * Cv + rv * u + rz1 * h,
        c * V + rr * g + rz1 * X1,
        c * pseudonym + rv * N ])

    return c == c_prime

#####################################################
# TASK Q1 -- Answer the following question:
#
# How could you use a credential scheme, such as the one you
# implemented above to implement an electronic cash scheme
# ensuring both integrity (no-double spending) and privacy. 
# What would the credential represent, and what statements
# would need to be shown to a verifier.

""" Your answer here. """
