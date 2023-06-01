# Calculate approximations for Solmonoff Induction, Kolmorogrov complexity, and AIXI

# see https://www.nyu.edu/projects/barker/Iota/

import sys
import random
from itertools import product

ticker_max = 1000
output = list()
ticker = int()

# this function reverses the input but that is fine we can just append the string in reverse
# there maybe a shorter identity function but this will do as an upper bound.
length_of_an_identity_function = len(
    "1111010101001110101010010011010100100100111010101001110101010011010100101010100111010101001101010011010101001101010010101010011101010100111010101001101010010101010011101010100110101001101010100110101001010101001110101010011010100110101010011010100110101010011101010100111010101001110101010011101010100100110101001001101010010011010100100110101001010100111010101001101010011010101001101010011010101001101010010101001110101010011101010100110101001010101001110101010011010100110101010011010100101010100111010101001101010011010101001110101010011010100101010100101010011101010100110101001010100111010101001110101010011010100101010100111010101001101010010101001110101010011010100101010100101010011010100111010101001101010011010101001001010100110101001010100111010101001101010011010101001101010011010101001101010010101001110101010011101010100110101001010101001110101010011010100110101010011010100101010100111010101001101010011010101001110101010011010100101010100101010011101010100110101001010100111010101001110101010011010100101010100111010101001101010010101001110101010011010100101010100101010011010100111010101001101010011010101001001010100110101001010100111010101001101010010101001010100"
)

sys.setrecursionlimit(10000)


def I(x):
    return x


def K(x):
    def K1(y):
        return x
    return K1


def S(x):
    def S1(y):
        def S2(z):
            return x(z)(y(z))
        return S2
    return S1


def tick():
    global ticker
    ticker += 1
    if ticker_max is not None and ticker > ticker_max:
        raise TimeoutError()

def zero(c):
    def basis(f):
        # bit of a guess where to put these?
        tick()
        return f(S)(K)
    return c(basis)


def one(c):
    def bigleft(L):
        def left(l):
            def bigright(R):
                def right(r):
                    # bit of a guess where to put these?
                    tick()
                    return c(l(r))
                return R(right)
            return bigright
        return L(left)
    return bigleft


def trivial(x):
    return x(I)


def zot(string):
    def process(position, value):
        if position >= len(string):
            return value
        if string[position] == "0":
            return process(position + 1, value(zero))
        return process(position + 1, value(one))
    return process(0, trivial)

def interrogate(f):
    return f(I)(I)(I)(K)

def pr(ch):
    output.append(
        interrogate(ch)("0")("1")
    )
    return pr

def run(string, ticker_limit=None):
    global output
    output.clear()
    global ticker_max
    ticker_max = ticker_limit
    global ticker
    ticker *= 0
    try:
        zot(string)(K(K(K(K(K(K(I)))))))(pr)
    except TimeoutError:
        # has not terminated return 'None'
        return None
    except Exception:
        # hmmm.. this shouldn't happen...
        return "crash"

    # there will be some functions mixed in here, just ignore them
    output = [char for char in output if type(char) is str]
    return str("".join(output))


def test_zot():

    test_set = [
        ("1111010101001110101010010011010100100100111010101001110101010011010100101010100111010101001101010011010101001"+
        "1010100101010100111010101001110101010011010100101010100111010101001101010011010101001101010010101010011101010"+
        "1001101010011010101001101010011010101001110101010011101010100111010101001110101010010011010100100110101001001"+
        "1010100100110101001010100111010101001101010011010101001101010011010101001101010010101001110101010011101010100"+
        "1101010010101010011101010100110101001101010100110101001010101001110101010011010100110101010011101010100110101"+
        "0010101010010101001110101010011010100101010011101010100111010101001101010010101010011101010100110101001010100"+
        "1110101010011010100101010100101010011010100111010101001101010011010101001001010100110101001010100111010101001"+
        "1010100110101010011010100110101010011010100101010011101010100111010101001101010010101010011101010100110101001"+
        "1010101001101010010101010011101010100110101001101010100111010101001101010010101010010101001110101010011010100"+
        "1010100111010101001110101010011010100101010100111010101001101010010101001110101010011010100101010100101010011"+
        "010100111010101001101010011010101001001010100110101001010100111010101001101010010101001010100"+
        "11101", "10111")
    ]
    for program, expected_result in test_set:
        actual_result = run(program)
        assert actual_result == expected_result, f"Expected {expected_result} but found {actual_result}"

def program_generator(max_length=float("inf")):
    """
    Generator for all zot programs
    :param max_length:
    :return:
    """
    program_length = 0
    while program_length <= max_length:
        for program in product([0, 1], repeat=program_length):
            program = "".join(str(x) for x in program)
            yield program
        program_length += 1


def kolmorogrov(input, q):
    """

    Compute an upper-bound estimate for Kolmorogrov complexity, using the language zot.
    As q->inf kolmorogrov(input, q) -> K(input)

    In practice very large programs are required for any non-trivial (i.e. non-empty) output. It is unlikely this
    function will ever return even for very simple input. (will need to check on the order of 10^356 programs)

    (see https://en.wikipedia.org/wiki/Iota_and_Jot)

    :param input: the input string to produce
    :param q: the number of 'ticks' to process per program before ignoring their output
    :return: a time-limited upper-bound to K_zot(input)
    """

    # run all programs and see what they generate
    c = length_of_an_identity_function

    for program in program_generator(c+length_of_an_identity_function):
        result = run(program, q)
        if result == input:
            return len(program)

    return c + len(input)

def solomonoff(input, program_length_limit=20):
    """
    (see https://wiki.lesswrong.com/wiki/Solomonoff_induction)

    how this should work: run an inifinite string of fair-coin tosses through a prefix universal turing machine
    and determine the probability it will output 'input' and then terminate.

    ... what I'm actually doing ...

    looking for all programs that are consistent with input, and using a weighted sum of these to predict next character

    """

    count_0 = 0
    count_1 = 0

    for program in program_generator(program_length_limit):
        # look for programs that generate then input, then another symbol, then halt
        # I really don't get why it has to halt though, if it outputs 001101 when we've seen 001 why is that a problem?
        result = run(program, 10000)
        if result is None or result == "crash":
            continue
        if len(result) > len(input) and result[:len(input)] == input:
            if result[len(input)] == "1":
                count_1 += 1 / 2**len(program)
            else:
                count_0 += 1 / 2**len(program)

    if count_0 + count_1 == 0:
        return -1
    else:
        return count_1 / (count_1 + count_0)

def zot_search():
    """
    look for interesting results
    :return:
    """

    # looking for:
    # programs that output longer than their length
    # programs that infinite loop (or loop more than 10k)

    for program in program_generator(50):
        result = run(program, 10000)
        if result == "crash":
            #print(f"[Crash] {program}")
            pass
        elif result is None:
            print(f"[Timeout] {program}")
        elif len(result) >= len(program):
            print(f"[{result}] {program}")
        # potential identity programs ??
        # elif len(result) >= 4 and (program[-len(result):] == result or program[-len(result):] == result[::-1]):
        #     print(f"[IDENT? {result}] {program}")

def zot_random_search():
    """
    Just a random search variant to see if there are any short programs that produce output...
    (or infinite loop)
    """

    # run all programs and see what they generate
    for _ in range(10000):
        program_length = random.randint(0, 10)
        program = random.choices(["0", "1"], k = program_length)
        program = "".join(program)

        result = run(program, 10000)

        if result is None:
            print(f"Program {program} did not terminate in time")
        elif result != "":
            print(f"Program {program} returned {result}")

    print("Finished checking")

if __name__ == "__main__":
    test_zot()

    #s = '0000'
    #print(f"K('{s}') <= {kolmorogrov(s, 10000)}")

    zot_search()

    # 20 gets 0.44, 0.33, 1.0! 0.71 (note the probability of 1 goes up sometimes)
    # 24 gets 0.43, 0.33, 0.99, 0.63 (hmm doesn't change too much...)

    # test_set = ["", "0", "00", "000"]
    # for input in test_set:
    #     prob = solomonoff(input, 30)
    #     print(f"'{input}' probability next symbol is 1 is {prob:.2f}")