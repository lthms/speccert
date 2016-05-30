Require Export SpecCert.Address.Address_ind.

Inductive HardwareAddress :=
| dram: Address -> HardwareAddress
| vga: Address -> HardwareAddress.
