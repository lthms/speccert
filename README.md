# SpecCert

SpecCert is a framework for specifying and verifying Hardware-based Security
Enforcement (HSE) mechanisms against hardware architecture models. HSE
mechanisms form a class of security enforcement mechanism such that a set of
trusted software components relies on hardware functions to enforce a security
policy.

SpecCert has been described in an academic paper submitted to [Formal Methods
2016 conference](http://fm2016.cs.ucy.ac.cy/). The formalism used in this code
is slightly different from the one described in the paper. We plan to update it
as soon as we can, but please notice that it will not affect the core proofs.

You can compile SpecCert using Coq v8.5pl1. Using another version of the proof
assistant will probably cause the build to fail.

```bash
make       # verify the SpecCert implementation
```
