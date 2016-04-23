############ Authors: ################################
#       Marcin Cuber
#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 03
#
# Basics of Privacy Friendly Computations through
#         Additive Homomorphic Encryption.
#
# Run the tests through:
# $ py.test -v test_file_name.py

#####################################################
# TASK 1 -- Setup, key derivation, log
#           Encryption and Decryption
#

from petlib.ec import EcGroup

def setup():
    """Generates the Cryptosystem Parameters."""
    G = EcGroup(nid=713)
    g = G.hash_to_point(b"g")
    h = G.hash_to_point(b"h")
    o = G.order()
    return (G, g, h, o)

def keyGen(params):
   """ Generate a private / public key pair """
   (G, g, h, o) = params
   
   priv = o.random() 
   pub = priv * g
   return (priv, pub)

def encrypt(params, pub, m):
    """ Encrypt a message under the public key """
    if not -100 < m < 100:
        raise Exception("Message value to low or high.")
    (G, g, h, o) = params
    
    priv = o.random()
    a = priv * g
    b = priv * pub + m * h
    c= (a,b)
    return c

def isCiphertext(params, ciphertext):
    """ Check a ciphertext """
    (G, g, h, o) = params
    ret = len(ciphertext) == 2
    a, b = ciphertext
    ret &= G.check_point(a)
    ret &= G.check_point(b)
    return ret

_logh = None
def logh(params, hm):
    """ Compute a discrete log, for small number only """
    global _logh
    (G, g, h, o) = params

    # Initialize the map of logh
    if _logh == None:
        _logh = {}
        for m in range (-1000, 1000):
            _logh[(m * h)] = m

    if hm not in _logh:
        raise Exception("No decryption found.")

    return _logh[hm]

def decrypt(params, priv, ciphertext):
    """ Decrypt a message using the private key """
    assert isCiphertext(params, ciphertext)
    (a , b) = ciphertext
    a = priv * a
    hm = b-a    

    return logh(params, hm)

#####################################################
# TASK 2 -- Define homomorphic addition and
#           multiplication with a public value
# 

def add(params, pub, c1, c2):
    """ Given two ciphertexts compute the ciphertext of the 
        sum of their plaintexts.
    """
    assert isCiphertext(params, c1)
    assert isCiphertext(params, c2)
   
    #zero element encrypted
    new_enc = encrypt(params, pub, 0)
    #check whether this new element is in fact 
    assert isCiphertext(params, new_enc)
    
    #assign variables to input ciphers
    (a0,b0)=c1
    (a1,b1)=c2
    #new generated 0 element cipher used for verification
    (a2,b2)=new_enc
    #compute initial addition of ciphers c1 + c2
    c3 = (a0+a1,b0+b1)
    #assign value to the new cipher
    (a3,b3) = c3
    #add zero element cipher encrypted with public key (pub)
    c3 = (a3+a2,b3+b2)
    return c3

def mul(params, pub, c1, alpha):
    """ Given a ciphertext compute the ciphertext of the 
        product of the plaintext time alpha """
    assert isCiphertext(params, c1)
    #zero element encrypted
    new_enc = encrypt(params, pub, 0)
    #check whether this new element is in fact
    assert isCiphertext(params, new_enc)
    #new generated 0 element cipher used for verification
    (a2,b2)=new_enc
    
    if alpha == 0:
        return (0+a2,0+b2)
        
    elif alpha == 1:
        (a0,b0) = c1
        #adding zero element
        c3 = (a0+a2,b0+b2)
        return c3
        
    elif alpha > 1:
        (a0, b0) = c1
        c2 = c1
        for i in range(1,alpha):
            (a1,b1) = c2
            c2 = (a1+a0,b1+b0)
        c3 = c2
        #assign values of cipher text to variable
        (a3,b3) = c3
        #add zero element cipher encrypted with public key (pub)
        c3 = (a3+a2,b3+b2)
    return c3

#####################################################
# TASK 3 -- Define Group key derivation & Threshold
#           decryption. Assume an honest but curious 
#           set of authorities.

def groupKey(params, pubKeys=[]):
    """ Generate a group public key from a list of public keys """
    (G, g, h, o) = params
    #let pub be equal to the first public key in the list
    pub = pubKeys[0]
    #scan through the rest of the list and add public keys
    for key in pubKeys[1:]:
        pub = pub+key
    return pub

def partialDecrypt(params, priv, ciphertext, final=False):
    """ Given a ciphertext and a private key, perform partial decryption. 
        If final is True, then return the plaintext. """
    assert isCiphertext(params, ciphertext)
    (a,b) = ciphertext
    a1 = priv*a
    b1 = b-a1
    if final:
        return logh(params, b1)
    else:
        return a, b1

#####################################################
# TASK 4 -- Actively corrupt final authority, derives
#           a public key with a known private key.
#

def corruptPubKey(params, priv, OtherPubKeys=[]):
    """ Simulate the operation of a corrupt decryption authority. 
        Given a set of public keys from other authorities return a
        public key for the corrupt authority that leads to a group
        public key corresponding to a private key known to the
        corrupt authority. """
    (G, g, h, o) = params

    #How it works:
    #Assume we are given g^x1, g^x2, g^x3, g^x4
    #what we need is something which we can decrypt using our private key priv
    #what we can do is inverse all the given public keys and add our public key
    #so we have (g^x1 * g^x2 * g^x3 * gx4 ) * (g^-x1 * g^-x2 * g^-x3 * g^-x4 * g^x5) = g^x5 which we can decrypt


    #-key is the inverse of the key
    pub=-OtherPubKeys[0]
    for key in OtherPubKeys[1:]:
        pub+=-key

    #add the public key
    pub+=priv*g

    return pub

#####################################################
# TASK 5 -- Implement operations to support a simple
#           private poll.
#

def encode_vote(params, pub, vote):
    """ Given a vote 0 or 1 encode the vote as two
        ciphertexts representing the count of votes for
        zero and the votes for one."""
    assert vote in [0, 1]
    #encrypt votes
    v0 = encrypt(params,pub,1-vote)
    v1 = encrypt(params,pub,vote)
    
    return (v0, v1)

def process_votes(params, pub, encrypted_votes):
    """ Given a list of encrypted votes tally them
        to sum votes for zeros and votes for ones. """
    assert isinstance(encrypted_votes, list)
    #zero element encrypted
    new_enc = encrypt(params, pub, 0)
    #assign variables to zero element ciphers
    (a2,b2)=new_enc
    #pick first vote from list 
    vote0 = encrypted_votes[0]
    #slit the first vote into two, vote for zero and for one resepectively
    sum_v0 = vote0[0]
    sum_v1 = vote0[1]
    #asign variable to each ciphertext(vote=0 or vote=1)
    (a0,b0) = sum_v0 
    (a1,b1) = sum_v1
    #scan through the rest of the vote tuples and do the same as above but then add it to a0,b0 and b0,b1
    for vote in encrypted_votes[1:]:
        temp0 = vote[0]
        temp1 = vote[1]
        (t00,t01) = temp0
        (t10,t11) = temp1
        (a0,b0) = (a0+t00,b0+t01)
        (a1,b1) = (a1+t10,b1+t11)
    #assign summed ciphertexts to v1 and v2 to return with added zero cipher texted
    v1 = (a0+a2,b0+b2)
    v2 = (a1+a2,b1+b2)
    return v1,v2

def simulate_poll(votes):
    """ Simulates the full process of encrypting votes,
        tallying them, and then decrypting the total. """

    # Generate parameters for the crypto-system
    params = setup()

    # Make keys for 3 authorities
    priv1, pub1 = keyGen(params)
    priv2, pub2 = keyGen(params)
    priv3, pub3 = keyGen(params)
    pub = groupKey(params, [pub1, pub2, pub3])

    # Simulate encrypting votes
    encrypted_votes = []
    for v in votes:
        encrypted_votes.append(encode_vote(params, pub, v))

    # Tally the votes
    total_v0, total_v1 = process_votes(params, pub, encrypted_votes)

    # Simulate threshold decryption
    privs = [priv1, priv2, priv3]
    for priv in privs[:-1]:
        total_v0 = partialDecrypt(params, priv, total_v0)
        total_v1 = partialDecrypt(params, priv, total_v1)

    total_v0 = partialDecrypt(params, privs[-1], total_v0, True)
    total_v1 = partialDecrypt(params, privs[-1], total_v1, True)

    # Return the plaintext values
    return total_v0, total_v1
