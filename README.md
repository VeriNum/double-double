# A Formally Verified Library of Double-Word Arithmetic
Copyright (c) 2023 Ariel Kellison

This library is open-source licensed according to the LGPL (Gnu Lesser General
Public License) version 3 or any later version.

## Repository map

- **dd_lib/**: A C library for double-double arithmetic.
- **Accuracy.v**: round-off error analysis for double-word operations.
- **TwoSum_acc.v**: correctness and accuracy of the TwoSum algorithm.
- **Fast2Mult_acc.v**: correctness and accuracy of the TwoSum algorithm.
- **verif_twoSum.v**: A VST proof of correctness of the TwoSum C implementation (i.e., /dd_lib/TwoSum.c). 
- **common/**: files with lemmas and tactics used across main analysis files.

## How to build 
- ** 

## References
The relevant reference for the research effort is ["Formalization of Double-Word Arithmetic, and Comments
on `Tight and Rigorous Error Bounds for Basic Building
Blocks of Double-Word Arithmetic' "](https://dl-acm-org.proxy.library.cornell.edu/doi/pdf/10.1145/3484514) by JEAN-MICHEL MULLER and LAURENCE RIDEAU. The Coq proofs from this reference can be found in the directory [paper_proofs](https://github.com/VeriNum/double-double/tree/main/paper_proofs). There are no dependencies on these proofs in the repository. 
