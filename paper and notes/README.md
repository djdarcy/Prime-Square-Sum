# Paper and Notes: Recurrence Relation Investigation

This subdirectory contains research notes and computational models exploring a potential recurrence relation between **Triangular Numbers** and **Squared Primes**.

## Broad Outlines of the Research

The investigation, started in 2010 and updated through 2026, seeks to answer whether a recursive series exists that links the sum of digits in the rows of triangular numbers to specific powers of prime numbers.

### Core Observations

1. **Triangular and Prime Link**: The initial observation centers on $\text{tri}(4) = 10$, where 10 is the sum of the first three primes ($2^1 + 3^1 + 5^1$).

2. **Higher Order Patterns**: Moving to a larger scale, $\text{tri}(36) = 666$, where 666 is the sum of the first seven squared primes ($2^2 + 3^2 + 5^2 + 7^2 + 11^2 + 13^2 + 17^2$).

3. **Recursive Footprints**: The notebook explores whether these "tri-row-sum sequences" are part of a deeper recursive series, potentially in base-666 or other higher bases.

## Key Functions & Visualizations

The notebook defines several critical functions to visualize and calculate these patterns:

- [**function-tf-defined.png**](function-tf-defined.png): Represents the **Triangular Function (tf)**. This relates to the standard triangular number formula $\frac{n^2+n}{2}$ and its geometric representation as a sequence of rows.

- [**function-stf-defined.png**](function-stf-defined.png): Represents the **Summed Triangular Function (stf)**. This is the core of the investigation—calculating the sum of the rows within a triangular number footprint to identify potential prime-power recurrences.

## Mathematica Notebook Details

The file [2010 - Recurrence relation between triangular numbers and squared primes - D. Darcy.nb](<2010 - Recurrence relation between triangular numbers and squared primes - D. Darcy.nb>) includes:

- **Symbolic Definitions**: Precise Mathematica functions for `RowReverse`, `LeftEdge`, and triangular summations.
- **Visualization Modules**: Code to generate the geometric diagrams and digit footprints used to identify the "666" connection.
- **Outstanding Questions**: A section dedicated to the unproven hypothesis regarding whether higher triangular row sums always equal sums of $p$-power primes.

### Usage

To explore the calculations, open the `.nb` file in **Wolfram Mathematica** or **Wolfram Player**. The notebook is structured to be interactive, allowing you to test higher values of $n$ to see if the prime-power recurrence holds.
