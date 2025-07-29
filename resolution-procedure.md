Problem: Binder's notion of causality is susceptible to the "gap problem".

We believe that the if we want to determine which events are influenced by the variation, we need to consider both execution traces. 

Consider two traces $\alpha$ and $\beta$ where $\alpha$ has a single variation compared to $\beta$. We explore a causality links in $\alpha$

The definition of causality is expected to have the following properties:
1. **Reachability** - any event which position is different between $\alpha$ and $\beta$ must be causally linked to the variation.
2. **Correctness** - if event is reachable via causal links, it has different timestamps between $\alpha$ and $\beta$.
3. **Forwardness** - given a causality link $e_1 \rightarrow e_2$, $e_1$ happens earlier than $e_2$ in trace $\alpha$.

First, the reachability does not hold in Binder's definition due to the gap problem.

TODO: other properties?

> Proposition: the intuitive understanding of causality is "event A was moved and because of that some event B was moved". "Moved" means that timestamp changed between traces. Initial event movement corresponds to a variation.

TODO: rewrite following

Set of constraints:

set of rules, defining how the events have to be placed in time (considering other events)

resolution procedure: move event according to variation, move events with broken constraints, ...

TODO: set of rules
