############ Author:################################
#       Marcin Cuber
#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 01
#
# Basics of Petlib, encryption, signatures and
# an end-to-end encryption system.
#
# Run the tests through:
# $ py.test-2.7 -v Lab01Tests.py 


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
    
    aes = Cipher("aes-128-gcm")
    iv = urandom(16)
    # Encryption using AES-GCM returns a ciphertext and a tag
    ciphertext, tag = aes.quick_gcm_enc(K, iv, plaintext) 
    

    return (iv, ciphertext, tag)

def decrypt_message(K, iv, ciphertext, tag):
    """ Decrypt a cipher text under a key K 

        In case the decryption fails, throw an exception.
    """
    aes = Cipher("aes-128-gcm")
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

    if x == None and y == None:
        return True

    lhs = (y * y) % p
    rhs = (x*x*x + a*x + b) % p
    on_curve = (lhs == rhs)

    return on_curve


def point_add(a, b, p, x0, y0, x1, y1):
    """Define the "addition" operation for 2 EC Points.

    Reminder: (xr, yr) = (xq, yq) + (xp, yp)
    is defined as:
        lam = yq - yp * (xq - xp)^-1 (mod p)
        xr  = lam^2 - xp - xq (mod p)
        yr  = lam * (xp - xr) - yp (mod p)

    Return the point resulting from the addition. Raises an Exception if the points are equal.
    """
    #initilise new coordinates
    xr, yr = None, None
    
    #create tuples for the input points
    p1 = (x0,y0)
    p2 = (x1,y1)
    
    #check validity of the points
    try:
        assert is_point_on_curve(a, b, p, x0, y0)
        assert is_point_on_curve(a, b, p, x1, y1)
    except:
        raise Exception('not valid points')

    #check curve 4a^3+27b^2 != 0 mod p.
    c0 = a.mod_pow(Bn(3),p)
    c1 = c0.mod_mul(Bn(4),p)
    c2 = b.mod_pow(Bn(2),p)
    c3 = c2.mod_mul(Bn(27),p)
    c = c1.mod_add(c3,p)
    try:
        assert c != 0
    except:
        raise Exception('invalid curve')
   
    #check if points are equal
    try:
        assert p1 != p2
    except:
        raise Exception('EC Points must not be equal')   
    
    #checking the points and different cases
    if p1 == (None,None) and p2 == (None, None):
        return (None,None)
    elif (x0 == x1) and (y0.mod_add(y1,p)==0):
        return (None,None)
    elif (x0 == None or y0 == None) and (x1 != None and y1 != None):
        return p2
    elif (x1 == None or y1 == None) and (x0 != None and y0 != None):
        return p1
    
    elif y0 != None and x0 != None and y1 != None and x1 != None:
        #check if the points are valid with an additional check
        #through an exception
        try:
            assert p1 != p2
            assert p1 != (x1,(-y1))
        except:
            raise Exception('EC Points must not be equal')
        if y1 == 0:
            lam0 = -y0
        else: 
            lam0 = y1.mod_sub(y0,p) 
        if x1 == 0:
            lam1 = -x0
        else:
            lam1 = x1.mod_sub(x0,p)
            
        #condition check if the gradient is 0
        if lam0 == 0 or lam1 == 0:
            xr = -x0.mod_sub(x1,p)
            yr = -y1
            #check if the point is on the curve
            if xr == None or yr == None:
                return (None, None)
            try:
                assert is_point_on_curve(a, b, p, xr, yr)
            except:
                raise Exception('The new point is not valid')
        #do calculations on the numbers that can give valid xr,yr point    
        else:
            lam2 = lam1.mod_inverse(p) 
            lam = lam0.mod_mul(lam2,p)
            xr0 = lam.mod_pow(Bn(2),p)
       
            xr1 = xr0.mod_sub(x0,p)
            xr = xr1.mod_sub(x1,p)
        
            yr0 = x0.mod_sub(xr,p)
            yr1 = lam.mod_mul(yr0,p)
            yr = yr1.mod_sub(y0,p)
            #check if the new point is valid and if it is then return it
            try:
                assert is_point_on_curve(a, b, p, xr, yr)
            except:
                raise Exception('The new point is not valid')
            #check if any part is None, it may never be!
            if xr == None or yr == None:
                return (None, None)
    return (xr, yr)

def point_double(a, b, p, x, y):
    """Define "doubling" an EC point.
     A special case, when a point needs to be added to itself.

     Reminder:
        lam = 3 * x ^ 2 + a * (2 * y) ^ -1 (mod p)
        xr  = lam ^ 2 - 2 * xp
        yr  = lam * (xp - xr) - yp (mod p)

    Returns the point representing the double of the input (x, y).
    """
    xr, yr = None, None
    p1 = (x,y)
    #check the input point for validity
    try:
        assert is_point_on_curve(a, b, p, x, y)
    except:
        raise Exception('not a valid point')
        
    #check curve 4a^3+27b^2 != 0 mod p for validity.
    c0 = a.mod_pow(Bn(3),p)
    c1 = c0.mod_mul(Bn(4),p)
    c2 = b.mod_pow(Bn(2),p)
    c3 = c2.mod_mul(Bn(27),p)
    c = c1.mod_add(c3,p)
    try:
        assert c != 0
    except:
        raise Exception('invalid curve')

    #verify the input point
    if p1 == (None,None):
        return (None,None)
    elif p1 == (0,0):
        return (0,0)
    elif y == None or y == 0:
        return (None, None)
    #calculate the new point== doubled point
    else:
        if x == 0:
            xp2 = a
        else:
            xp0 = x.mod_pow(Bn(2),p)
            xp1 = xp0.mod_mul(Bn(3),p)
            xp2 = xp1.mod_add(a,p)
       
        yp0 = y.mod_mul(Bn(2),p)
        
        if yp0 != 0:
            yp = yp0.mod_inverse(p)
        else:
            yp = 0;
        if (xp2 != 0 and yp != 0):
            #calculate gradient if the points are not zero
            lam = xp2.mod_mul(yp,p)
            
            #calculate new x coordinate
            xr0 = lam.mod_pow(Bn(2),p)
            xr1 = x.mod_mul(Bn(2),p)
            xr = xr0.mod_sub(xr1,p)
            
            #calcualte new y coordinate
            yr0 = x.mod_sub(xr,p)
            yr1 = lam.mod_mul(yr0,p)
            yr = yr1.mod_sub(y,p)
            
            if (xr == None or yr == None):
                return (None, None)
        else:
            xr = -x.mod_mul(Bn(2),p)
            yr = -y
            if (xr == None or yr == None):
                return (None, None)
        
        #check whether the new point is valid whcih is passed from the previous if statement
        try:
            assert is_point_on_curve(a, b, p, x, y)
        except:
            raise Exception('The new point is not valid')
    return xr, yr

def point_scalar_multiplication_double_and_add(a, b, p, x, y, scalar):
    """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        Q = infinity
        for i = 0 to num_bits(P)-1
            if bit i of P == 1 then
                Q = Q + P
            P = 2 * P
        return Q
    """
    Q = (None, None)
    P = (x, y)
    binary = bin(scalar)
    
    for i in range(scalar.num_bits()):

        if binary[scalar.num_bits()-i+1] == '1':
            Q = point_add(a, b, p, Q[0], Q[1], P[0], P[1])
            #print Q
            pass
        P = point_double(a, b, p, P[0],P[1])
        pass
    return Q

def point_scalar_multiplication_montgomerry_ladder(a, b, p, x, y, scalar):
    """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        R0 = infinity
        R1 = P
        for i in num_bits(P)-1 to zero:
            if di = 0:
                R1 = R0 + R1
                R0 = 2R0
            else
                R0 = R0 + R1
                R1 = 2 R1
        return R0

    """
    R0 = (None, None)
    R1 = (x, y)
    #convert the scalar variable to binary
    binary = bin(scalar)
    #start the scan checking each bit 
    for i in reversed(range(0,scalar.num_bits())):
        #if bit is 0 do the addition and double R0
        if binary[scalar.num_bits()-i+1] == '0':
            R1 = point_add(a, b, p, R0[0], R0[1], R1[0], R1[1])
            R0 = point_double(a, b, p, R0[0],R0[1])
        #if bit is not zero then do the addition and double R1
        else:
            R0 = point_add(a, b, p, R0[0], R0[1], R1[0], R1[1])
            R1 = point_double(a, b, p, R1[0],R1[1])
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
    digest = sha256(plaintext).digest()
    sig = do_ecdsa_sign(G,priv_sign,digest)

    return sig

def ecdsa_verify(G, pub_verify, message, sig):
    """ Verify the ECDSA signature on the message """
    plaintext =  message.encode("utf8")
    digest = sha256(plaintext).digest()
    res = do_ecdsa_verify(G,pub_verify,sig,digest) 

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


def dh_encrypt(pub, message):
    """ Assume you know the public key of someone else (Bob), 
    and wish to Encrypt a message for them.
        - Generate a fresh DH key for this message.
        - Derive a fresh shared key.
        - Use the shared key to AES_GCM encrypt the message.
        - Optionally: sign the message.
    """
    
    Group, private, public = dh_get_key()#generate new DH pair for Alice
    #private key is an integer/scalar and public key is a point on the curve 
    
    #check whether public key of Bob is valid and on curve 
    assert Group.check_point(pub)
    
    #Alice obtains shared secret by multiplying her private key with bob's forwarded public key
    key = pub.pt_mul(private)#dA* qB
    print "key from enc is", key
    
    hashedKey=sha256(key.export()).digest()

    
    plaintext = message.encode("utf8")#encode message
    aes = Cipher("aes-128-gcm")#select cipher
    iv = urandom(16)#generate initialization vector 
    cipher, tag = aes.quick_gcm_enc(hashedKey[:16], iv, plaintext)#encrypt using shared key  
    ciphertext = [iv,cipher,tag,public]

    return ciphertext

def dh_decrypt(priv, ciphertext):
    """ Decrypt a received message encrypted using your public key, 
    of which the private key is provided"""
    Group1,private, public = dh_get_key()#generate new DH pair for Bob
    iv=ciphertext[0]
    cipher=ciphertext[1]
    tag=ciphertext[2]
    pubA=ciphertext[3]
    
    #Bob derives shared secret key by multiplying his public key with Alice's private key
    shared2 = pubA.pt_mul(priv)#qA * dB
    print "key from dec is", shared2

    hashedKey=sha256(shared2.export()).digest()
    
    aes = Cipher("aes-128-gcm")
    plain = aes.quick_gcm_dec(hashedKey[:16], iv, cipher, tag)#where to get IV and tag from ???
    
    return plain.encode("utf8")
   
## NOTE: populate those (or more) tests
#  ensure they run using the "py.test filename" command.
#  What is your test coverage? Where is it missing cases?
#  $ py.test --cov-report html --cov Lab01Code Lab01Code.py -s

def test_encrypt():
    G1, private1, public1 = dh_get_key()
    msg = u"Test" * 1000
    print "msg is"
    ciphertext=dh_encrypt(public1,msg)
    assert True

def test_decrypt():
    G1, private1, public1 = dh_get_key()
    msg = u"Test" * 1000
    print "decnow"
    ciphertext=dh_encrypt(public1,msg)

    assert dh_decrypt(private1,ciphertext)==msg

def test_fails():
    G1, private1, public1 = dh_get_key()
    msg = u"Test" * 1000
    ciphertext=dh_encrypt(public1,msg)
    iv=ciphertext[0]#get IV from dh_encrypt()
    tag=ciphertext[2]#tag
    pubA=ciphertext[3]#Alice's public key
    
    #derive shared secret by doing qA * dB 
    shared=pubA.pt_mul(private1)
    hashedKey=sha256(shared.export()).digest()
    print "shared in fail is", shared
    
    mess=msg.encode("utf8")
    aes = Cipher.aes_128_gcm()          # Initialize AES cipher
    enc = aes.enc(hashedKey[:16], iv)           # Get an encryption CipherOperation
    ciphertext2 = enc.update(mess)  # Include some plaintext
    nothing = enc.finalize()            # Finalize
    tag2 = enc.get_tag(16)               # Get the AES-GCM tag
    
    if tag==tag2:#only attempt to decrypt if tag is valid !
        assert dh_decrypt(private1,ciphertext)==mess
    else: 
        assert False 

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
    pass
