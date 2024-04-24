def powerBasisOfFiniteOfSeparable : PowerBasis F E :=
  let α := (exists_primitive_element F E).choose
  let pb := adjoin.powerBasis (IsSeparable.isIntegral F α)
  have e : F⟮α⟯ = ⊤ := (exists_primitive_element F E).choose_spec
  pb.map ((IntermediateField.equivOfEq e).trans IntermediateField.topEquiv)
#align field.power_basis_of_finite_of_separable Field.powerBasisOfFiniteOfSeparable