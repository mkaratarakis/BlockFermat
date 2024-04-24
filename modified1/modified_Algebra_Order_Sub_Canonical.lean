def CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid : AddCancelCommMonoid α :=
  { (by infer_instance : AddCommMonoid α) with
    add_left_cancel := fun a b c h => by
      simpa only [add_tsub_cancel_left] using congr_arg (fun x => x - a) h }
#align canonically_ordered_add_monoid.to_add_cancel_comm_monoid CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid