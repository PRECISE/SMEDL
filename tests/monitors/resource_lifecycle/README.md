Resource Lifecycle
==================

Based on benchmark 4.3.18 from CRV 14:

Bartocci, E., Falcone, Y., Bonakdarpour, B. et al. First international
Competition on Runtime Verification: rules, benchmarks, tools, and final
results of CRV 2014. Int J Softw Tools Technol Transfer 21, 31–70 (2019).
https://doi.org/10.1007/s10009-017-0454-5

This monitor tracks the lifecycle of resources. Free resources may be
requested. Requested resources may be denied (making them free again) or
granted. Granted resources may be canceled (making them free again) or
rescinded (in which case they remain granted). Any other actions are
violations.

If any resources are granted when the end event arrives, that is a violation.
