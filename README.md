# Comparison of Domain Finding Algorithms

Hi­C is an experimental protocol that allows us to measure pairwise physical proximity between different regions of the genome. The results of Hi­C experiments have led to a number of discoveries about the large ­scale structure of the genome and how it is folded in the cell, and has uncovered important relationships between genome structure and function.
One of the hallmark structures uncovered by Hi­C data are chromatin “domains”. These
domains are densely ­packed regions of chromatin that are correlated with gene expression and different types of genomic signals (e.g. chromatin markers). These domains have also been shown to be evolutionarily conserved, which further suggests their biological importance. Several papers have been published suggesting computational methods for finding these domains from Hi­C data. Although some comparisons are done within the publications, a complete view of how the results from these algorithms differ is not detailed.

This project aims to, first, implement the following algorithms:
<ol>
<li>Armatus (implementation available) [1]</li>
<li>Dixon domain finding (implementation available) [2]</li>
<li>2D segmentation of Hi­C data (needs to be re­implemented*) [3]</li>
<li>Arrowhead algorithm (needs to be implemented**) [4]</li>
</ol>

*The source code for this algorithm is available in C but the program is barely understandable and therefore needs to be re­implemented, possibly with some changes.

**The algorithm is explained in the supplementary material of this paper but an implementation is not available.

After these have been implemented, results from these are to be generated and compared.
Some suggested tests (although not limited to these) include enrichment testing, domain
conservation between mouse and human datasets, comparison against randomized data and
functional enrichment testing using GO terms. Data and code for some of these tests is available.
