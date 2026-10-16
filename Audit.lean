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
