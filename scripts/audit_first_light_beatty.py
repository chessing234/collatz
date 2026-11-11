#!/usr/bin/env python3
"""Recheck the finite Beatty gap and first-crossing witnesses independently."""


THRESHOLD = 3_997_765


def audit_gap() -> None:
    coefficient, accumulator = 1, 0
    for count in range(8_951):
        lower_power = 1 << (coefficient.bit_length() - 1)
        assert accumulator + coefficient * THRESHOLD < 2 * lower_power * THRESHOLD
        accumulator = 3 * accumulator + lower_power
        coefficient *= 3
    assert 2**14_186 < coefficient


def audit_small_inputs() -> None:
    longest = (0, 0)
    for source in range(3, THRESHOLD, 2):
        value, coefficient, denominator = source, 1, 1
        for step in range(1, 225):
            if value % 2:
                value = (3 * value + 1) // 2
                coefficient *= 3
            else:
                value //= 2
            denominator *= 2
            if coefficient < denominator:
                assert value < source, (source, step, value)
                longest = max(longest, (step, source))
                break
        else:
            raise AssertionError((source, "no crossing in the verified horizon"))
    assert longest[0] == 224
    print(f"Checked every odd source below {THRESHOLD:,}. Longest first crossing was {longest}.")


if __name__ == "__main__":
    audit_gap()
    audit_small_inputs()
