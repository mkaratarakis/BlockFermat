def multiplicity.addValuation (hp : Prime p) : AddValuation R PartENat :=
  AddValuation.of (multiplicity p) (multiplicity.zero _) (one_right hp.not_unit)
    (fun _ _ => min_le_multiplicity_add) fun _ _ => multiplicity.mul hp
#align multiplicity.add_valuation multiplicity.addValuation