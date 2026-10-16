import LatinQuarter

#print LatinQuarter.IsLatin
#print LatinQuarter.IsDefining
#print LatinQuarter.IsCritical
#print LatinQuarter.scs
#print LatinQuarter.scsOf
#check LatinQuarter.defining_set_lower_bound
#check LatinQuarter.quarter_bound
#check LatinQuarter.scs_eq_quarter
#check LatinQuarter.cyclic_scs_eq_quarter
#check LatinQuarter.completions_card_even

-- Theorems A and B restated with the paper's own definitions (Textbook.lean)
#print LatinQuarter.Textbook.Latin
#print LatinQuarter.Textbook.Completes
#print LatinQuarter.Textbook.numCompletions
#print LatinQuarter.Textbook.DefiningSet
#print LatinQuarter.Textbook.CriticalSet
#print LatinQuarter.Textbook.scsOf
#print LatinQuarter.Textbook.scs
#print LatinQuarter.Textbook.cyclicSquare
#check LatinQuarter.Textbook.completions_even
#check LatinQuarter.Textbook.definingSet_card
#check LatinQuarter.Textbook.scs_eq_quarter

/-- info: 'LatinQuarter.defining_set_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.defining_set_lower_bound

/-- info: 'LatinQuarter.cornerSet_isDefining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.cornerSet_isDefining

/-- info: 'LatinQuarter.cornerSet_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.cornerSet_card

/-- info: 'LatinQuarter.scs_eq_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.scs_eq_quarter

/-- info: 'LatinQuarter.cyclic_scs_eq_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.cyclic_scs_eq_quarter

/-- info: 'LatinQuarter.quarter_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.quarter_bound

/-- info: 'LatinQuarter.completions_card_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.completions_card_even

/-- info: 'LatinQuarter.Textbook.completions_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.Textbook.completions_even

/-- info: 'LatinQuarter.Textbook.definingSet_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.Textbook.definingSet_card

/-- info: 'LatinQuarter.Textbook.scs_eq_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LatinQuarter.Textbook.scs_eq_quarter
