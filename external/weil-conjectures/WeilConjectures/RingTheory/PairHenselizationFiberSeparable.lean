/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.PairHenselizationFiltered
import WeilConjectures.RingTheory.PairHenselizationEssentiallySmall
import WeilConjectures.RingTheory.ProEtale.IndEtale

/-!
# Separability of pair henselization residue fields

Source: Stacks Project, More on Algebra, Tag 0AH1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Separability of ring elements implies separability of every residue-field fraction. -/
private theorem isSeparable_residueField_of_images
    {B k : Type*} [CommRing B] [Field k] (q : Ideal B) [q.IsPrime]
    [Algebra k q.ResidueField]
    (h : ∀ b : B, IsSeparable k (algebraMap B q.ResidueField b)) :
    Algebra.IsSeparable k q.ResidueField := by
  refine ⟨fun y ↦ ?_⟩
  rw [← mem_separableClosure_iff (F := k) (E := q.ResidueField)]
  obtain ⟨x', m', _, hxm⟩ := IsFractionRing.div_surjective (A := B ⧸ q) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x'
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m'
  rw [← hxm, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk]
  exact div_mem (mem_separableClosure_iff.mpr (h x))
    (mem_separableClosure_iff.mpr (h m))

/-- The canonical residue extension of a Noetherian pair henselization is separable algebraic.

Source: Stacks Project, More on Algebra, Tag 0AH1; Tag 0A02 for filteredness.
(blueprint: lem-weil-pbc-pair-henselization-fiber-separable).

Proof: Filteredness and essential smallness of the pair-etale neighborhood category
show that the given colimit structure map is ind-etale. Use the characterization of
ind-morphisms by essentially small filtered presentations in the under-category;
each diagram object is etale by its defining property. For an element b of the
colimit ring, the proved source-library lemma
`Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing` shows that its image in
q.ResidueField is separable over p.ResidueField. The residue map rho supplies the
compatible scalar tower because it is an A-algebra map. Every residue-field element
is a fraction of two images of ring elements: first use its fraction-field description
over B/q, then lift numerator and denominator through the quotient map. Both belong
to the separable closure, and that field is closed under division. This proves
separability of every residue-field element, hence the stated algebraic separability.
This argument does not use Noetherianity or the finite product decomposition. -/
theorem pair_henselization_fiber_separable
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun D : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) [IsNoetherianRing c.pt.right]
    (q : Ideal c.pt.right) [q.IsPrime] :
    letI := c.pt.hom.hom.toAlgebra
    let p := q.comap c.pt.hom.hom
    ∀ (ρ : p.ResidueField →ₐ[A] q.ResidueField),
      ρ = Ideal.ResidueField.mapₐ p q (Algebra.ofId A c.pt.right) rfl →
      letI := ρ.toRingHom.toAlgebra
      Algebra.IsSeparable p.ResidueField q.ResidueField := by
  let _ := c.pt.hom.hom.toAlgebra
  let P : ObjectProperty (Under (CommRingCat.of A)) := fun D ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
      Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
        Ideal.le_comap_map)
  let _ : EssentiallySmall.{u} P.FullSubcategory := pair_henselization_essentiallySmall A I
  let _ : IsFiltered P.FullSubcategory := pair_henselization_filtered A I
  have hind : c.pt.hom.hom.IndEtale := by
    rw [RingHom.IndEtale.iff_ind_etale, MorphismProperty.ind_iff_ind_underMk]
    change ObjectProperty.ind.{u} CommRingCat.etale.underObj c.pt
    apply ObjectProperty.of_essentiallySmall_index
      (pres := { diag := P.ι, ι := c.ι, isColimit := hc })
    intro j
    change RingHom.Etale j.obj.hom.hom
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mp j.property.1
  have : Algebra.IndEtale A c.pt.right := hind
  dsimp only
  intro ρ hρ
  let _ := ρ.toRingHom.toAlgebra
  have : IsScalarTower A (q.comap c.pt.hom.hom).ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' ρ.comp_algebraMap.symm
  have key (b : c.pt.right) :
      IsSeparable (q.comap c.pt.hom.hom).ResidueField
        (algebraMap c.pt.right q.ResidueField b) :=
    Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing
      (q.comap c.pt.hom.hom).ResidueField q.ResidueField
      (IsScalarTower.toAlgHom A c.pt.right q.ResidueField) b
  exact isSeparable_residueField_of_images q key

end RingTheory
