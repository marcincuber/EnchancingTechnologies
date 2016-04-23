############ Author:################################
#       Marcin Cuber
#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 02
#
# Basics of Mix networks and Traffic Analysis
#
# Run the tests through:
# $ py.test -v test_file_name.py

#####################################################
# TASK 1 -- Ensure petlib is installed on the System
#           and also pytest. Ensure the Lab Code can 
#           be imported.

from collections import namedtuple
from hashlib import sha512
from struct import pack, unpack
from binascii import hexlify

def aes_ctr_enc_dec(key, iv, input):
    """ A helper function that implements AES Counter (CTR) Mode encryption and decryption. 
    Expects a key (16 byte), and IV (16 bytes) and an input plaintext / ciphertext.

    If it is not obvious convince yourself that CTR encryption and decryption are in 
    fact the same operations.
    """
    
    aes = Cipher("AES-128-CTR")
    enc = aes.enc(key, iv)
    output = enc.update(input)
    output += enc.finalize()

    return output

#####################################################
# TASK 2 -- Build a simple 1-hop mix client.
#
#


## This is the type of messages destined for the one-hop mix
OneHopMixMessage = namedtuple('OneHopMixMessage', ['ec_public_key', 
                                                   'hmac', 
                                                   'address', 
                                                   'message'])

from petlib.ec import EcGroup
from petlib.hmac import Hmac, secure_compare
from petlib.cipher import Cipher

def mix_server_one_hop(private_key, message_list):
    """ Implements the decoding for a simple one-hop mix. 

        Each message is decoded in turn:
        - A shared key is derived from the message public key and the mix private_key.
        - the hmac is checked against all encrypted parts of the message
        - the address and message are decrypted, decoded and returned

    """
    G = EcGroup()

    out_queue = []

    # Process all messages
    for msg in message_list:

        ## Check elements and lengths
        if not G.check_point(msg.ec_public_key) or \
               not len(msg.hmac) == 20 or \
               not len(msg.address) == 258 or \
               not len(msg.message) == 1002:
           raise Exception("Malformed input message")

        ## First get a shared key
        shared_element = private_key * msg.ec_public_key
        key_material = sha512(shared_element.export()).digest()

        # Use different parts of the shared key for different operations
        hmac_key = key_material[:16]
        address_key = key_material[16:32]
        message_key = key_material[32:48]
        
        ## Check the HMAC
        h = Hmac(b"sha512", hmac_key)        
        h.update(msg.address)
        h.update(msg.message)
        expected_mac = h.digest()

        if not secure_compare(msg.hmac, expected_mac[:20]):
            raise Exception("HMAC check failure")

        ## Decrypt the address and the message
        iv = b"\x00"*16

        address_plaintext = aes_ctr_enc_dec(address_key, iv, msg.address)
        message_plaintext = aes_ctr_enc_dec(message_key, iv, msg.message)

        # Decode the address and message
        address_len, address_full = unpack("!H256s", address_plaintext)
        message_len, message_full = unpack("!H1000s", message_plaintext)

        output = (address_full[:address_len], message_full[:message_len])
        out_queue += [output]

    return sorted(out_queue)
        
        
def mix_client_one_hop(public_key, address, message):
    """
    Encode a message to travel through a single mix with a set public key. 
    The maximum size of the final address and the message are 256 bytes and 1000 bytes respectively.
    Returns an 'OneHopMixMessage' with four parts: a public key, an hmac (20 bytes),
    an address ciphertext (256 + 2 bytes) and a message ciphertext (1002 bytes). 
    """

    G = EcGroup()
    assert G.check_point(public_key)
    assert isinstance(address, bytes) and len(address) <= 256
    assert isinstance(message, bytes) and len(message) <= 1000

    # Encode the address and message
    # Use those as the payload for encryption
    address_plaintext = pack("!H256s", len(address), address)
    message_plaintext = pack("!H1000s", len(message), message)

    ## Generate a fresh public key
    private_key = G.order().random()
    client_public_key  = private_key * G.generator()
    
    # generate shared element
    shared = public_key.pt_mul(private_key)
    material = sha512(shared.export()).digest()
    
    # split shared key for different operations
    hmac_key = material[:16]
    address_key = material[16:32]
    message_key = material[32:48]
    
    # random inistialisation vector
    iv = b"\x00"*16
    
    # encoding address and message
    address_cipher = aes_ctr_enc_dec(address_key, iv, address_plaintext)
    message_cipher = aes_ctr_enc_dec(message_key, iv, message_plaintext)
    
    # generate hmac h
    h = Hmac(b"sha512",hmac_key)
    h.update(address_cipher)
    h.update(message_cipher)
    expected_mac = h.digest()
    expected_mac = expected_mac[:20]

    return OneHopMixMessage(client_public_key, expected_mac, address_cipher, message_cipher)

    

#####################################################
# TASK 3 -- Build a n-hop mix client.
#           Mixes are in a fixed cascade.
#

from petlib.ec import Bn

# This is the type of messages destined for the n-hop mix
NHopMixMessage = namedtuple('NHopMixMessage', ['ec_public_key', 
                                                   'hmacs', 
                                                   'address', 
                                                   'message'])


def mix_server_n_hop(private_key, message_list, final=False):
    """ Decodes a NHopMixMessage message and outputs either messages destined
    to the next mix or a list of tuples (address, message) (if final=True) to be 
    sent to their final recipients.

    Broadly speaking the mix will process each message in turn: 
        - it derives a shared key (using its private_key), 
        - checks the first hmac,
        - decrypts all other parts,
        - Either forwards or decodes the message. 
    """

    G = EcGroup()

    out_queue = []

    # Process all messages
    for msg in message_list:

        ## Check elements and lengths
        if not G.check_point(msg.ec_public_key) or \
               not isinstance(msg.hmacs, list) or \
               not len(msg.hmacs[0]) == 20 or \
               not len(msg.address) == 258 or \
               not len(msg.message) == 1002:
           raise Exception("Malformed input message")

        ## First get a shared key
        shared_element = private_key * msg.ec_public_key
        key_material = sha512(shared_element.export()).digest()

        # Use different parts of the shared key for different operations
        hmac_key = key_material[:16]
        address_key = key_material[16:32]
        message_key = key_material[32:48]

        # Extract a blinding factor for the public_key
        blinding_factor = Bn.from_binary(key_material[48:])
        new_ec_public_key = blinding_factor * msg.ec_public_key


        ## Check the HMAC
        h = Hmac(b"sha512", hmac_key)

        for other_mac in msg.hmacs[1:]:
            h.update(other_mac)

        h.update(msg.address)
        h.update(msg.message)

        expected_mac = h.digest()

        if not secure_compare(msg.hmacs[0], expected_mac[:20]):
            raise Exception("HMAC check failure")

        ## Decrypt the hmacs, address and the message
        aes = Cipher("AES-128-CTR") 

        # Decrypt hmacs
        new_hmacs = []
        for i, other_mac in enumerate(msg.hmacs[1:]):
            # Ensure the IV is different for each hmac
            iv = pack("H14s", i, b"\x00"*14)

            hmac_plaintext = aes_ctr_enc_dec(hmac_key, iv, other_mac)
            new_hmacs += [hmac_plaintext]

        # Decrypt address & message
        iv = b"\x00"*16
        
        address_plaintext = aes_ctr_enc_dec(address_key, iv, msg.address)
        message_plaintext = aes_ctr_enc_dec(message_key, iv, msg.message)

        if final:
            # Decode the address and message
            address_len, address_full = unpack("!H256s", address_plaintext)
            message_len, message_full = unpack("!H1000s", message_plaintext)

            out_msg = (address_full[:address_len], message_full[:message_len])
            out_queue += [out_msg]
        else:
            # Pass the new mix message to the next mix
            out_msg = NHopMixMessage(new_ec_public_key, new_hmacs, address_plaintext, message_plaintext)
            out_queue += [out_msg]

    return out_queue


def mix_client_n_hop(public_keys, address, message):
    """
    Encode a message to travel through a sequence of mixes with a sequence public keys. 
    The maximum size of the final address and the message are 256 bytes and 1000 bytes respectively.
    Returns an 'NHopMixMessage' with four parts: a public key, a list of hmacs (20 bytes each),
    an address ciphertext (256 + 2 bytes) and a message ciphertext (1002 bytes). 

    """
    G = EcGroup()
    assert isinstance(address, bytes) and len(address) <= 256
    assert isinstance(message, bytes) and len(message) <= 1000

    # Encode the address and message
    # use those encoded values as the payload you encrypt!
    address_plaintext = pack("!H256s", len(address), address)
    message_plaintext = pack("!H1000s", len(message), message)

    ## Generate a fresh public key
    private_key = G.order().random()
    client_public_key  = private_key * G.generator()
    
    # initilise lists for hmacs and blinding_keys
    hmacs = []
    blinding_keys = []
    
    # initilise variables
    address_cipher = address_plaintext
    message_cipher = message_plaintext
    
    # initial blinding_factor set to 1
    blinding_factor = Bn(1)
    
    # append first public key to list
    blinding_keys.append(public_keys[0])
    length = len(public_keys)
    
    for i in range(1, length):
        # generate shared element
        shared = private_key * blinding_keys[-1]
        material = sha512(shared.export()).digest()
        
        # generate another bliding factor
        blinding_factor = blinding_factor * Bn.from_binary(material[48:])
        
        # calculate and append blinding factor to a list
        public_key = public_keys[i]
        blinding_keys = blinding_keys + [blinding_factor * public_key]
    
    # In reverse order calculate message for each hop using generated blinding factors
    blinding_keys = reversed(blinding_keys)
    for key in blinding_keys:
        # generate shared element
        shared = private_key * key
        material = sha512(shared.export()).digest()
        
        # split shared key for different operations
        hmac_key = material[:16]
        address_key = material[16:32]
        message_key = material[32:48]
        
        # random inistialisation vector
        iv = b"\x00"*16
    
        # encoding address and message
        address_cipher = aes_ctr_enc_dec(address_key, iv, address_cipher)
        message_cipher = aes_ctr_enc_dec(message_key, iv, message_cipher)
        
        # temporary list of hmacs
        temp_hmacs = []
        h = Hmac(b"sha512", hmac_key)
        
        for i in range(0,len(hmacs)):
            prev_mac = hmacs[i]
            # Ensure the IV is different for each hmac
            iv = pack("H14s", i, b"\x00"*14)
            
            # encode
            hmac_plaintext = aes_ctr_enc_dec(hmac_key, iv, prev_mac)
            # add the encoded hmac to the temporary list
            temp_hmacs = temp_hmacs + [hmac_plaintext]
            h.update(hmac_plaintext)
    
        h.update(address_cipher)
        h.update(message_cipher)
        
        # turn h into binary
        expected_mac = h.digest()
        # take first 20 bits
        expected_mac = expected_mac[:20]
        # insert expected_mac (final mac) to the beggining of the list
        temp_hmacs = [expected_mac] + temp_hmacs
        
        # update hmacs list with temp_hmacs list
        hmacs = temp_hmacs
        
    return NHopMixMessage(client_public_key, hmacs, address_cipher, message_cipher)



#####################################################
# TASK 4 -- Statistical Disclosure Attack
#           Given a set of anonymized traces
#           the objective is to output an ordered list
#           of likely `friends` of a target user.

import random

def generate_trace(number_of_users, threshold_size, number_of_rounds, targets_friends):
    """ Generate a simulated trace of traffic. """
    target = 0
    others = range(1, number_of_users)
    all_users = range(number_of_users)

    trace = []
    
    ## Generate traces in which Alice (user 0) is not sending
    for _ in range(number_of_rounds // 2):
        senders = sorted(random.sample( others, threshold_size))
        receivers = sorted(random.sample( all_users, threshold_size))

        trace += [(senders, receivers)]
    
    ## Generate traces in which Alice (user 0) is sending
    for _ in range(number_of_rounds // 2):
        senders = sorted([0] + random.sample( others, threshold_size-1))
        # Alice sends to a friend
        friend = random.choice(targets_friends)
        receivers = sorted([friend] + random.sample( all_users, threshold_size-1))

        trace += [(senders, receivers)]

    random.shuffle(trace)
    return trace


from collections import Counter

def analyze_trace(trace, target_number_of_friends, target=0):
    """ 
    Given a trace of traffic, and a given number of friends, 
    return the list of receiver identifiers that are the most likely 
    friends of the target.
    """
    # Solution
    # Trace when alice is in the senders list
    # Trace when alice is not in the senders list
    # For each receiver, check the difference in these counts.

    # initial data: set up Counter collections to hold the stats:
    # count those who received
    # while alice was sending
    receivers_a = Counter()
    
    # count those who received
    # while alice was not sending
    receivers_not_a = Counter()
    
    # constructed during analysis to hold the differences
    receiver_difference = Counter()
    
    # Stage one, count the number of times the receiver was referenced
    for t in trace[:]:
        senders, receivers = t
        if target in senders:
            for receiver in receivers:
                receivers_a[receiver] +=  1
        else:
            for receiver in receivers:
                receivers_not_a[receiver] +=  1

    # Stage 2, process the stats

    for receiver in list(receivers_a):
        print "receiver", receiver, " count of receivers_a",receivers_a[receiver], "count of receivers_not_a",receivers_not_a[receiver]
        print "receiver", receiver, " count of receivers_a",receivers_a[receiver], "count of receivers_not_a",receivers_not_a[receiver]
        receiver_difference[receiver] = receivers_a[receiver] - receivers_not_a[receiver]
    
    # Stage 3, construct a list as a return code
    
    outcomes = []
    for counter in list(receiver_difference.most_common(target_number_of_friends)):
        identifier,count = counter
        outcomes = outcomes + [identifier]
    
    return outcomes


