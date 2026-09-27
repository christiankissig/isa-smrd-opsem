# EventStruct — SMRD event-structure semantics (reusable ★ — AFP candidate)

Events, preserved program order `ppo`, semantic dependency `DP`, executions; futures `Φ`,
histories, posterior futures, `horizonΦ_H`, episodicity. Defines the Φ/horizon interface the
operational semantics consults; **MoRDor** is the computational oracle that produces concrete
Φ per program.

**Status:** built, zero `sorry`. Parameterised over the abstract action/label types from `Core`.
