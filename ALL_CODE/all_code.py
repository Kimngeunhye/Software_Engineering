from sha256 import generate_hash
from md5 import md5_me
import doctest
import unittest
import inspect
import sys
from types import FrameType, TracebackType
from typing import Any, Optional, Callable, Dict, List, Type, TextIO, cast
from collections.abc import Generator
from math import sin

counters = {
    'generate_hash' : 0,
    'md5_me' : 0
}
#hash_generate
K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

def generate_hash(message: bytearray) -> bytearray:

    global counters
    counters['generate_hash'] += 1
    
    if isinstance(message, str):
        message = bytearray(message, 'ascii')
    elif isinstance(message, bytes):
        message = bytearray(message)
    elif not isinstance(message, bytearray):
        raise TypeError

    # Padding
    length = len(message) * 8 # len(message) is number of BYTES!!!
    message.append(0x80)
    while (len(message) * 8 + 64) % 512 != 0:
        message.append(0x00)

    message += length.to_bytes(8, 'big') # pad to 8 bytes or 64 bits

    assert (len(message) * 8) % 512 == 0, "Padding did not complete properly!"

    # Parsing
    blocks = [] # contains 512-bit chunks of message
    for i in range(0, len(message), 64): # 64 bytes is 512 bits
        blocks.append(message[i:i+64])

    # Setting Initial Hash Value
    h0 = 0x6a09e667
    h1 = 0xbb67ae85
    h2 = 0x3c6ef372
    h3 = 0xa54ff53a
    h5 = 0x9b05688c
    h4 = 0x510e527f
    h6 = 0x1f83d9ab
    h7 = 0x5be0cd19

    # SHA-256 Hash Computation
    for message_block in blocks:
        # Prepare message schedule
        message_schedule = []
        for t in range(0, 64):
            if t <= 15:
                # adds the t'th 32 bit word of the block,
                # starting from leftmost word
                # 4 bytes at a time
                message_schedule.append(bytes(message_block[t*4:(t*4)+4]))
            else:
                term1 = _sigma1(int.from_bytes(message_schedule[t-2], 'big'))
                term2 = int.from_bytes(message_schedule[t-7], 'big')
                term3 = _sigma0(int.from_bytes(message_schedule[t-15], 'big'))
                term4 = int.from_bytes(message_schedule[t-16], 'big')

                # append a 4-byte byte object
                schedule = ((term1 + term2 + term3 + term4) % 2**32).to_bytes(4, 'big')
                message_schedule.append(schedule)

        assert len(message_schedule) == 64

        # Initialize working variables
        a = h0
        b = h1
        c = h2
        d = h3
        e = h4
        f = h5
        g = h6
        h = h7

        # Iterate for t=0 to 63
        for t in range(64):
            t1 = ((h + _capsigma1(e) + _ch(e, f, g) + K[t] +
                   int.from_bytes(message_schedule[t], 'big')) % 2**32)

            t2 = (_capsigma0(a) + _maj(a, b, c)) % 2**32

            h = g
            g = f
            f = e
            e = (d + t1) % 2**32
            d = c
            c = b
            b = a
            a = (t1 + t2) % 2**32

        # Compute intermediate hash value
        h0 = (h0 + a) % 2**32
        h1 = (h1 + b) % 2**32
        h2 = (h2 + c) % 2**32
        h3 = (h3 + d) % 2**32
        h4 = (h4 + e) % 2**32
        h5 = (h5 + f) % 2**32
        h6 = (h6 + g) % 2**32
        h7 = (h7 + h) % 2**32

    return ((h0).to_bytes(4, 'big') + (h1).to_bytes(4, 'big') +
            (h2).to_bytes(4, 'big') + (h3).to_bytes(4, 'big') +
            (h4).to_bytes(4, 'big') + (h5).to_bytes(4, 'big') +
            (h6).to_bytes(4, 'big') + (h7).to_bytes(4, 'big'))

def _sigma0(num: int):
    """As defined in the specification."""
    num = (_rotate_right(num, 7) ^
           _rotate_right(num, 18) ^
           (num >> 3))
    return num

def _sigma1(num: int):
    """As defined in the specification."""
    num = (_rotate_right(num, 17) ^
           _rotate_right(num, 19) ^
           (num >> 10))
    return num

def _capsigma0(num: int):
    """As defined in the specification."""
    num = (_rotate_right(num, 2) ^
           _rotate_right(num, 13) ^
           _rotate_right(num, 22))
    return num

def _capsigma1(num: int):
    """As defined in the specification."""
    num = (_rotate_right(num, 6) ^
           _rotate_right(num, 11) ^
           _rotate_right(num, 25))
    return num

def _ch(x: int, y: int, z: int):
    """As defined in the specification."""
    return (x & y) ^ (~x & z)

def _maj(x: int, y: int, z: int):
    """As defined in the specification."""
    return (x & y) ^ (x & z) ^ (y & z)

def _rotate_right(num: int, shift: int, size: int = 32):
    """Rotate an integer right."""
    return (num >> shift) | (num << size - shift)

#md5
def to_little_endian(string_32: bytes) -> bytes:
    if len(string_32) != 32:
        raise ValueError("Input must be of length 32")

    little_endian = b""
    for i in [3, 2, 1, 0]:
        little_endian += string_32[8 * i : 8 * i + 8]
    return little_endian


def reformat_hex(i: int) -> bytes:
    if i < 0:
        raise ValueError("Input must be non-negative")

    hex_rep = format(i, "08x")[-8:]
    little_endian_hex = b""
    for i in [3, 2, 1, 0]:
        little_endian_hex += hex_rep[2 * i : 2 * i + 2].encode("utf-8")
    return little_endian_hex


def preprocess(message: bytes) -> bytes:
    bit_string = b""
    for char in message:
        bit_string += format(char, "08b").encode("utf-8")
    start_len = format(len(bit_string), "064b").encode("utf-8")

    # Pad bit_string to a multiple of 512 chars
    bit_string += b"1"
    while len(bit_string) % 512 != 448:
        bit_string += b"0"
    bit_string += to_little_endian(start_len[32:]) + to_little_endian(start_len[:32])

    return bit_string


def get_block_words(bit_string: bytes) -> Generator[list[int], None, None]:
    if len(bit_string) % 512 != 0:
        raise ValueError("Input must have length that's a multiple of 512")

    for pos in range(0, len(bit_string), 512):
        block = bit_string[pos : pos + 512]
        block_words = []
        for i in range(0, 512, 32):
            block_words.append(int(to_little_endian(block[i : i + 32]), 2))
        yield block_words


def not_32(i: int) -> int:
    if i < 0:
        raise ValueError("Input must be non-negative")

    i_str = format(i, "032b")
    new_str = ""
    for c in i_str:
        new_str += "1" if c == "0" else "0"
    return int(new_str, 2)


def sum_32(a: int, b: int) -> int:
    return (a + b) % 2**32


def left_rotate_32(i: int, shift: int) -> int:
    if i < 0:
        raise ValueError("Input must be non-negative")
    if shift < 0:
        raise ValueError("Shift must be non-negative")
    return ((i << shift) ^ (i >> (32 - shift))) % 2**32
import hashlib

def md5_me(message:str) -> str:
    global counters
    counters['md5_me'] += 1
    hash_value = ""
    if isinstance(message, str):
        hash_value = hashlib.md5(message.encode()).hexdigest()
    else:
        raise TypeError
    return hash_value
    # Convert to bit string, add padding and append message length
    bit_string = preprocess(message)

    added_consts = [int(2**32 * abs(sin(i + 1))) for i in range(64)]

    # Starting states
    a0 = 0x67452301
    b0 = 0xEFCDAB89
    c0 = 0x98BADCFE
    d0 = 0x10325476

    shift_amounts = [
        7,
        12,
        17,
        22,
        7,
        12,
        17,
        22,
        7,
        12,
        17,
        22,
        7,
        12,
        17,
        22,
        5,
        9,
        14,
        20,
        5,
        9,
        14,
        20,
        5,
        9,
        14,
        20,
        5,
        9,
        14,
        20,
        4,
        11,
        16,
        23,
        4,
        11,
        16,
        23,
        4,
        11,
        16,
        23,
        4,
        11,
        16,
        23,
        6,
        10,
        15,
        21,
        6,
        10,
        15,
        21,
        6,
        10,
        15,
        21,
        6,
        10,
        15,
        21,
    ]

    # Process bit string in chunks, each with 16 32-char words
    for block_words in get_block_words(bit_string):
        a = a0
        b = b0
        c = c0
        d = d0
        
        result = {
            'a': a,
            'b': b,
            'c': c,
            'd': d,
            }


        # Hash current chunk
        for i in range(64):
            if i <= 15:
                # f = (b & c) | (not_32(b) & d)     # Alternate definition for f
                f = d ^ (b & (c ^ d))
                g = i
            elif i <= 31:
                # f = (d & b) | (not_32(d) & c)     # Alternate definition for f
                f = c ^ (d & (b ^ c))
                g = (5 * i + 1) % 16
            elif i <= 47:
                f = b ^ c ^ d
                g = (3 * i + 5) % 16
            else:
                f = c ^ (b | not_32(d))
                g = (7 * i) % 16
            f = (f + a + added_consts[i] + block_words[g]) % 2**32
            a = d
            d = c
            c = b
            b = sum_32(b, left_rotate_32(f, shift_amounts[i]))

        # Add hashed chunk to running total
        a0 = sum_32(a0, a)
        b0 = sum_32(b0, b)
        c0 = sum_32(c0, c)
        d0 = sum_32(d0, d)

    digest = reformat_hex(a0) + reformat_hex(b0) + reformat_hex(c0) + reformat_hex(d0)
    return result

def print_counters():
    global counters
    for func_name, count in counters.items():
        print(f"{func_name}: {count}")
        
class LVVTracer():
    def __init__(self, file:TextIO = sys.stdout) -> Dict:
        self.last_vars: Dict[str, Any] = {}
        #object().__init__(file = file)
    
    def __enter__(self) -> Any:
        self.original_trace_function = sys.gettrace()
        sys.settrace(self._traceit)
        return self
    
    def __exit__(self, exc_tp: Type, exc_value:BaseException, exc_traceback:TracebackType) -> Optional[bool]:
        sys.settrace(self.original_trace_function)
        if self.is_internal_error(exc_tp, exc_value, exc_traceback):
            return False
        else:
            return None
    
    def getLVVmap(self, new_vars:Dict[str, Any]) -> Dict[str, Any]:
        changed = {}
        for var_name, var_value in new_vars.items():
            if (var_name not in self.last_vars or self.last_vars[var_name] != var_value):
                changed[var_name] = var_value
        self.last_vars = new_vars.copy()
        return changed
    
    def test_lvv_sha256():
        with LVVTracer(target_func = "generate_hash") as traced:
            encoded = "mysalt".encode()
            generate_hash(encoded).hex()

        answer = {'t': 128, 'message_schedule': 65, 'a': 65, 'b': 65, 'c': 65, 'd': 65, 'e': 65, 'f': 65, 'g': 65, 'h': 65, 't1': 64, 't2': 64, 'message': 52, 'term1': 48, 'schedule': 48, 'term2': 43, 'term3': 36, 'term4': 36, 'blocks': 2, 'h0': 2, 'h1': 2, 'h2': 2, 'h3': 2, 'h5': 2, 'h4': 2, 'h6': 2, 'h7': 2, 'length': 1, 'i': 1, 'message_block': 1}
        assert traced.getLVVmap() == answer

    def test_lvv_md5():
        with LVVTracer(target_func = "md5_me") as traced:
            encoded = "mypepperoni".encode()
            md5_me(encoded).hex()

        answer = {'f': 128, 'a': 65, 'b': 65, 'c': 65, 'd': 65, 'i': 64, 'g': 64, 'a0': 2, 'b0': 2, 'c0': 2, 'd0': 2, 'message': 1, 'bit_string': 1, 'added_consts': 1, 'shift_amounts': 1, 'block_words': 1, 'digest': 1}
        assert traced.getLVVmap() == answer
        
def count_changes(original_str, modified_str):
    count_dict = {}
    for algorithm in ['md5', 'sha1', 'sha256']:
        hash_func = getattr(hashlib, algorithm)
        original_hash = hash_func(original_str.encode()).hexdigest()
        modified_hash = hash_func(modified_str.encode()).hexdigest()
        count = 0
        for i in range(len(original_hash)):
            if original_hash[i] != modified_hash[i]:
                count += 1
        count_dict[algorithm] = count
    return count_dict

original_str = "Hello, world!"
modified_str = "Hello, world!!"
count_dict = count_changes(original_str, modified_str)
print(count_dict)