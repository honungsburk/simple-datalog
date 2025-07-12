# Simple Datalog

I've struggled to build a datalog-inspired query engine for a language I'm creating, so 
as an intermediate step I'm implementing a simple datalog engine here without all the fuss.


## TODO

**Algorithms:**
- bottom-up
    - [x] naive
    - [x] semi-naive
        - I think we could do better because we backtrack to much
    - [ ] leapfrog trie-join
    - [ ] Magic Set
- top-down
    - [ ] Query Sub-Query (QSQ)
- Incremental 
    - [ ] Counting Algorithm for Non-recursive Queries
    - [ ] Delete and Re-Derive Algorithm
    - [ ] Provenance-based Incremental Maintanence
    - [ ] Incremental Maintenance for Negation and Aggregates
**Extensions:**
- [ x ] Stratified Negation
- [ ] Stratified Aggregation
- [ ] Functors?
- [ ] Expressions
**Improvements**
- [ ] Rewrite rules so that negation happens in the end automatically? If not then a rule that should produce tuples might not because a negative rule without bindings will eliminate all substitutions.

## Resources

- https://github.com/frankmcsherry/blog/blob/master/posts/2018-05-19.md
- http://blogs.evergreen.edu/sosw/files/2014/04/Green-Vol5-DBS-017.pdf