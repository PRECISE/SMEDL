Grant Cancel
============

Based on benchmark 4.3.16 from CRV 14:

Bartocci, E., Falcone, Y., Bonakdarpour, B. et al. First international
Competition on Runtime Verification: rules, benchmarks, tools, and final
results of CRV 2014. Int J Softw Tools Technol Transfer 21, 31–70 (2019).
https://doi.org/10.1007/s10009-017-0454-5

This monitor tracks resources granted to tasks. A resource may be granted to a
single task, which must later free it. It is a violation if:

1. A resource is granted to multiple tasks
2. A resource is cancelled by a task not holding it
