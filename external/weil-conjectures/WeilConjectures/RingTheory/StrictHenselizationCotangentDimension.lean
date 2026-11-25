/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Cotangent dimension and strict henselization

Source: Stacks Project, `more-algebra.tex`, Tag 06LN and Tag 07QM
(blueprint: lem-sc-strict-henselization-cotangent-dimension).
-/

@[expose] public section

universe u

namespace Algebra

/-- Transporting an ideal along an algebra equivalence preserves its cotangent module. -/
private theorem cotangent_bijective_equiv
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map e.toRingHom = J)
    (h : I ≤ J.comap e.toRingHom) :
    Function.Bijective (Ideal.mapCotangent I J e.toAlgHom h) := by
  have hJI : J.map e.symm.toRingHom = I := by
    rw [← hIJ, Ideal.map_map]
    have hid : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by
      ext a
      exact e.symm_apply_apply a
    rw [hid, Ideal.map_id]
  have h' : J ≤ I.comap e.symm.toRingHom := Ideal.map_le_iff_le_comap.mp hJI.le
  let f := Ideal.mapCotangent I J e.toAlgHom h
  let g := Ideal.mapCotangent J I e.symm.toAlgHom h'
  have hgf : Function.LeftInverse g f := by
    intro x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp only [f, g, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    exact e.symm_apply_apply x
  have hfg : Function.RightInverse g f := by
    intro x
    obtain ⟨x, rfl⟩ := J.toCotangent_surjective x
    simp only [f, g, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    exact e.apply_symm_apply x
  exact ⟨hgf.injective, hfg.surjective⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The flat conormal base-change map of Stacks Tag 0473, transported from `C ⊗[R] R`. -/
private theorem flat_cotangent_bijective
    {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] [Module.Flat R C]
    (I : Ideal R) (J : Ideal C) (hIJ : I.map (algebraMap R C) = J)
    (h : I ≤ J.comap (algebraMap R C)) :
    Function.Bijective (LinearMap.liftBaseChange C
      (Ideal.mapCotangent I J (Algebra.ofId R C) h)) := by
  let e := Algebra.TensorProduct.rid R C C
  let I' := I.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* _root_.TensorProduct R C R)
  have he : I'.map e.toRingHom = J := by
    rw [Ideal.map_map]
    have hid : e.toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom : R →+* _root_.TensorProduct R C R) =
        algebraMap R C := by
      ext r
      simp [e, Algebra.smul_def]
    rw [hid, hIJ]
  have hi : I' ≤ J.comap e.toRingHom := Ideal.map_le_iff_le_comap.mp he.le
  let g := Ideal.mapCotangent I' J e.toAlgHom hi
  have hg : Function.Bijective g := cotangent_bijective_equiv e I' J he hi
  have hf : Function.Bijective (I.tensorCotangentHom R C) :=
    ⟨I.tensorCotangentHom_injective_of_flat R C, I.tensorCotangentHom_surjective R C⟩
  have hcomp : LinearMap.liftBaseChange C (Ideal.mapCotangent I J (Algebra.ofId R C) h) =
      g.comp (I.tensorCotangentHom R C) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    dsimp only [LinearMap.comp_apply]
    rw [LinearMap.liftBaseChange_tmul, Ideal.tensorCotangentHom_tmul]
    simp only [g, I', map_smul, Ideal.mapCotangent_toCotangent]
    congr 1
    congr 1
    apply Subtype.ext
    simp [e, Algebra.smul_def]
  rw [hcomp]
  exact hg.comp hf

/-- A conormal base-change isomorphism induces an isomorphism over the residue fields. -/
private theorem cotangent_finrank_of_bijective
    {R C : Type*} [CommRing R] [IsLocalRing R] [CommRing C] [IsLocalRing C]
    [Algebra R C]
    (h : IsLocalRing.maximalIdeal R ≤
      (IsLocalRing.maximalIdeal C).comap (algebraMap R C))
    (hb : Function.Bijective (LinearMap.liftBaseChange C
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal C)
        (Algebra.ofId R C) h))) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
      Module.finrank (IsLocalRing.ResidueField C) (IsLocalRing.CotangentSpace C) := by
  classical
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField C
  let M := IsLocalRing.CotangentSpace R
  let N := IsLocalRing.CotangentSpace C
  have : IsLocalHom (algebraMap R C) :=
    ⟨fun x ↦ not_imp_not.mp (@h x)⟩
  have : TensorProduct.CompatibleSMul R k l M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective l M
      (IsLocalRing.residue_surjective (R := R))
  have : TensorProduct.CompatibleSMul C l l N :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective l N
      (IsLocalRing.residue_surjective (R := C))
  let e : _root_.TensorProduct R C M ≃ₗ[C] N := LinearEquiv.ofBijective _ hb
  let e' : _root_.TensorProduct k l M ≃ₗ[l] N :=
    (_root_.TensorProduct.equivOfCompatibleSMul R k l l M).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R C l l M).symm.trans
        ((e.baseChange C l _ _).trans (_root_.TensorProduct.lidOfCompatibleSMul C l N)))
  exact (Module.finrank_baseChange (R := l) (S := k) (M' := M)).symm.trans e'.finrank_eq

/-- A strict henselization `C` of a Noetherian local ring `R` is local, and the canonical
base-change map `(m_R/m_R²) ⊗ κ^sep → m_C/m_C²` is an isomorphism; it is written as the
canonical `C`-linear map `C ⊗[R] (m_R/m_R²) → m_C/m_C²` (the same map: `m_R` kills the source,
`m_R C = m_C`, and the residue field of `C` is `κ^sep`). In particular the cotangent-space
dimensions agree.
Source: Stacks Project, More on Algebra, Tag 06LN, using Tag 07QM.

Proof:
1. `strictHenselization_local_maximalIdeal` supplies locality and the maximal-ideal
   equality. `IsStrictHenselization.triples_presentation` presents the given algebra
   as the triples colimit, so `strictHenselization_faithfullyFlat` applies to its
   original structural map.
2. Apply `lem-weil-pbc-ideal-cotangent-flat-base-change-ring` to that flat map and
   the maximal ideal of `R`. This gives bijectivity of the canonical `C`-linear
   map from `C` tensored over `R` with the cotangent space of `R`.
3. Tensor the isomorphism with the residue field of `C`. Associativity cancels the
   intervening extension to `C`. Since the residue maps are surjective, compatible
   scalar actions identify the source with residue-field extension of the cotangent
   space of `R`, and identify the target with the cotangent space of `C`.
   `Module.finrank_baseChange` and invariance under linear equivalence give the
   dimension equality. This comparison also holds without finite dimensionality.
(blueprint: lem-sc-strict-henselization-cotangent-dimension). -/
theorem finrank_cotangentSpace_eq_of_isStrictHenselization
    (R K C : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C]
    (hC : IsStrictHenselization R K C) :
    ∃ _ : IsLocalRing C,
      (∃ h : IsLocalRing.maximalIdeal R ≤
          (IsLocalRing.maximalIdeal C).comap (algebraMap R C),
        Function.Bijective (LinearMap.liftBaseChange C
          (Ideal.mapCotangent (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal C)
            (Algebra.ofId R C) h))) ∧
        Module.finrank (IsLocalRing.ResidueField R)
            (IsLocalRing.CotangentSpace R) =
          Module.finrank (IsLocalRing.ResidueField C)
            (IsLocalRing.CotangentSpace C) := by
  classical
  obtain ⟨hlocal, hm⟩ := strictHenselization_local_maximalIdeal R K C hC
  have := hlocal
  obtain ⟨p, hp, a, hs, ι, ⟨hc⟩, hρ⟩ := hC.triples_presentation R K C
  let := a
  have := hs
  have hflat := AlgebraicGeometry.Scheme.strictHenselization_faithfullyFlat
    (CommRingCat.of R) p hp K (CategoryTheory.Limits.Cocone.mk (CommRingCat.of C) ι)
    hc (CommRingCat.ofHom (algebraMap R C)) hρ
  have : Module.FaithfullyFlat R C :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hflat
  have h : IsLocalRing.maximalIdeal R ≤
      (IsLocalRing.maximalIdeal C).comap (algebraMap R C) :=
    Ideal.map_le_iff_le_comap.mp hm.symm.le
  have hb := flat_cotangent_bijective (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal C) hm.symm h
  exact ⟨hlocal, ⟨h, hb⟩, cotangent_finrank_of_bijective h hb⟩

end Algebra
