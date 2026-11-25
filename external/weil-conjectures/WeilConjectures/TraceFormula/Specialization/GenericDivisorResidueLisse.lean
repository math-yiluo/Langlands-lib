/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalSchemeOpen
public import WeilConjectures.ConstructibleSheaf.SylowGaloisCoverTrivializing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceDegree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EllGroupMonodromyDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorFiniteCover
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorFiniteGeneric
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorFiniteTransfer
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorNormalization
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorResidueConstant

/-!

# Generic vanishing along a divisor for lisse finite coefficients

Let `X` be a normal scheme of finite type over a field `k`, `Z = V(h)` a principal
divisor, `j : U = X ∖ Z ⟶ X`, `ζ` a generic point of `Z`, and `K` a complex of `𝔽_E`-module
objects on `U` of étale origin `K ↔ F'`, where `F'` is a bounded complex of étale sheaves whose
cohomology sheaves are finite locally constant on `U`. Then `Le^* Ψ_X(j_! K)` vanishes near `ζ`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_residueField_of_lisse`).

## Proof

This is the blueprint argument of `lemma-vanishing-generic-points-principal-divisor--1`, with the
induction on the degree of a trivialising cover replaced by the `ℓ`-Sylow reduction:

* a finite étale `v : W ⟶ U` of degree `d` prime to `ℓ`, over which all `Hⁿ(F')` acquire finite
  `ℓ`-group monodromy (`Scheme.exists_sylow_galoisCover_trivializing`);
* `K` is a retract of `Rv_* Lv^* K` by the trace of `v`
  (`isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_geometricFiber_card`);
* `v` extends to the normalisation `f : X' ⟶ X` of `X` in `W`
  (`exists_normalization_of_finite_etale`), and `j_! Rv_* = Rf_* j'_!`
  (`nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso`);
* the proper exchange transfers the question to the points of `X'` over `ζ`
  (`nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite`), which are generic points of the
  divisor `f^* Z` of the normal scheme `X'`
  (`closure_singleton_mem_irreducibleComponents_of_centreMap`);
* on `X'` the dévissage of complexes with finite `ℓ`-group monodromy
  (`ProEtale.prop_of_isBoundedFiniteEllGroupMonodromy_finiteCoefficient`) reduces to `j'_! 𝔽_E`,
  which is the constant case (`nearbyCyclesVanishNear_lowerShriek_unit_residueField`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Helpers

/-- The geometric fibres of `e ≫ v` for an isomorphism `e` are in bijection with those of `v`. -/
lemma nat_card_geometricFiber_iso_comp {W W' U : Scheme.{u}} (e : W' ⟶ W) [IsIso e] (v : W ⟶ U)
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ U) :
    Nat.card ((e ≫ v).GeometricFiber s) = Nat.card (v.GeometricFiber s) :=
  Nat.card_congr
    { toFun x := ⟨x.1 ≫ e, by rw [Category.assoc, x.2]⟩
      invFun x := ⟨x.1 ≫ inv e, by rw [Category.assoc, IsIso.inv_hom_id_assoc, x.2]⟩
      left_inv x := Subtype.ext (by simp)
      right_inv x := Subtype.ext (by simp) }

end Helpers
variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- The complement `X ∖ V(h)` of the divisor of a nonzero function `h` on an integral scheme is
nonempty. -/
lemma nonempty_overRestrict_compl (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0)
    {I : X.left.IdealSheafData} (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h})) :
    Nonempty (overRestrict X I.support.compl).left := by
  have := hX.1
  have hsupp : (I.support : Set X.left) = X.left.zeroLocus (U := ⊤) {h} := by
    rw [← IdealSheafData.range_subschemeι, hI, IdealSheafData.range_subschemeι_ofIdealTop_span]
  obtain ⟨x, hx⟩ : ((X.left.basicOpen h : X.left.Opens) : Set X.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    exact hh ((basicOpen_eq_bot_iff h).1 (SetLike.coe_injective h0))
  have hxU : x ∈ I.support.compl := by
    change x ∉ (I.support : Set X.left)
    rw [hsupp, Scheme.mem_zeroLocus_iff]
    exact fun H ↦ H h rfl hx
  exact ⟨⟨x, hxU⟩⟩

-- The finite `ℓ`-group monodromy of the pulled-back étale model is checked degree by degree on
-- étale sheaves of `𝔽_E`-modules, whose instance search is slow.
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **Generic vanishing along a divisor for lisse finite coefficients** (blueprint
`lemma-vanishing-generic-points-principal-divisor--1`, lisse case): let `X` be normal, `Z = V(h)`,
`ζ` a generic point of `Z`, and `K` a complex of `𝔽_E`-module objects on `U = X ∖ Z` corresponding
to a bounded complex `F'` of étale sheaves with finite locally constant cohomology sheaves. Then
`Le^* Ψ_X(j_! K)` vanishes near `ζ`. -/
theorem nearbyCyclesVanishNear_lowerShriek_residueField_of_lisse
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology (overRestrict X I.support.compl).left)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))
        (overRestrict X I.support.compl).left)))
    (F' : DerivedCategory (Sheaf (overRestrict X I.support.compl).left.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1)))))
    (a b : ℤ) (ha : F'.IsGE a) (hb : F'.IsLE b)
    (hl : ∀ n : ℤ, IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj F'))
    (e : (finiteCoefficientDerivedEquivalence _ (integersResidueField ℓ E.1)).functor.obj K ≅
      D(ν^*((overRestrict X I.support.compl).left)[
        ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))]).obj F') :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
        Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj K) := by
  have := hX.1
  have : Nonempty (overRestrict X I.support.compl).left := nonempty_overRestrict_compl hX hh hI
  have : IsIntegral (overRestrict X I.support.compl).left :=
    isIntegral_of_isOpenImmersion (overRestrictι X I.support.compl).left
  have : CharP (integersResidueField ℓ E.1) ℓ :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (natCast_eq_zero_integersResidueField ℓ E.1)
  -- the `ℓ`-Sylow cover trivialising the cohomology sheaves
  have : ∀ i : Set.Icc a b, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ (i : ℤ)).obj F') := fun i ↦ hl i
  obtain ⟨W, v, _, _, _, d, hdℓ, hcard, G, _, _, hG, c, htriv⟩ :=
    Scheme.exists_sylow_galoisCover_trivializing (U := (overRestrict X I.support.compl).left) ℓ
      (fun i : Set.Icc a b ↦ (DerivedCategory.homologyFunctor _ (i : ℤ)).obj F')
  have hd : IsUnit (d : integersResidueField ℓ E.1) := by
    rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff _ ℓ]
    exact hdℓ
  have hsplit := isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_geometricFiber_card
    (integersResidueField ℓ E.1) v hd hcard K
  -- the finite `ℓ`-group monodromy of the pullback to `W`
  have hW : Etale.IsBoundedFiniteEllGroupMonodromy ℓ
      ((D(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) v)).obj
        F') := by
    refine ⟨⟨a, b, (Etale.upperStar _ v).isGE_mapDerivedCategory_obj F' a,
      (Etale.upperStar _ v).isLE_mapDerivedCategory_obj F' b⟩, fun n ↦ ?_⟩
    refine Etale.HasFiniteEllGroupMonodromy.of_iso ?_
      (((Etale.upperStar _ v).mapDerivedCategoryHomologyFunctorIso n).app F')
    by_cases hn : n ∈ Set.Icc a b
    · have ht := htriv ⟨n, hn⟩
      exact ⟨G, _, _, hG, c, ht.choose, ht.choose_spec.1, ht.choose_spec.2⟩
    · have hz : IsZero ((DerivedCategory.homologyFunctor _ n).obj F') := by
        rcases not_and_or.1 hn with hn | hn
        · exact (DerivedCategory.isGE_iff F' a).1 ha n (lt_of_not_ge hn)
        · exact (DerivedCategory.isLE_iff F' b).1 hb n (lt_of_not_ge hn)
      have : (Etale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) v).IsLeftAdjoint :=
        (Etale.upperStarLowerStarAdjunction _ v).isLeftAdjoint
      have h₀ := (Etale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) v).map_isZero hz
      have h₁ := (Etale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) c.π).map_isZero h₀
      have h₂ := (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1)))).map_isZero
        (ModuleCat.isZero_of_subsingleton
          (ModuleCat.of (ULift.{u + 1} (integersResidueField ℓ E.1)) PUnit))
      exact ⟨G, _, _, hG, c, _, inferInstance, ⟨h₁.iso h₂⟩⟩
  -- the normalisation of `X` in `W`, with `W ≅ U' = X' ∖ f⁻¹ Z`
  obtain ⟨X', _, _, _, f, _, w, _, hX', hsq⟩ := exists_normalization_of_finite_etale hX I v
  have hsq' : IsPullback (overRestrictι X' (I.comap f.left).support.compl).left (inv w ≫ v)
      f.left (overRestrictι X I.support.compl).left :=
    IsPullback.of_iso hsq (asIso w) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp)
  have hsplit := isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_geometricFiber_card
    (integersResidueField ℓ E.1) (inv w ≫ v) hd
    (fun Ω _ _ s ↦ (nat_card_geometricFiber_iso_comp (inv w) v s).trans (hcard Ω s)) K
  have hKo : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) _
      ((finiteCoefficientDerivedEquivalence _ (integersResidueField ℓ E.1)).functor.obj K) :=
    ⟨F', ⟨a, ha⟩, ⟨e.symm⟩⟩
  have hMo := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj _
    (inv w ≫ v) hKo
  have hjMo := ObjectProperty.prop_of_iso _
    ((finiteCoefficientDerivedOpenImmersionLowerShriekIso (integersResidueField ℓ E.1)
      (overRestrictι X' (I.comap f.left).support.compl).left).app _)
    (plusEtaleOrigin_mapDerivedCategory_openImmersionLowerShriek
      (overRestrictι X' (I.comap f.left).support.compl).left hMo)
  obtain ⟨eiso⟩ := nonempty_rightDerivedLowerStar_openImmersionLowerShriek_iso
    (integersResidueField ℓ E.1) f.left (overRestrictι X I.support.compl).left
    (overRestrictι X' (I.comap f.left).support.compl).left (inv w ≫ v) hsq' (centreι X I).left
    (isCompl_range_overRestrictι_centreι I).symm _ hjMo
  suffices hR : nearbyCyclesVanishNear X I k'
      (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      (R((f.left)_*⟦Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj
        (D(((overRestrictι X' (I.comap f.left).support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj
          (L((inv w ≫ v)^*⟦Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj
            K))) by
    let r : Retract K _ :=
      { i := (derivedUpperStarLowerStarAdjunction _ (inv w ≫ v)).unit.app K
        r := retraction ((derivedUpperStarLowerStarAdjunction _ (inv w ≫ v)).unit.app K)
        retract := IsSplitMono.id _ }
    exact (nearbyCyclesVanishNear X I k' _ ζ).prop_of_retract
      (r.map (D(((overRestrictι X I.support.compl).left)_!open⟦
        Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)))
      ((nearbyCyclesVanishNear X I k' _ ζ).prop_of_iso eiso hR)
  refine nearbyCyclesVanishNear_rightDerivedLowerStar_of_isFinite _ f I k' ζ _ hjMo
    fun ζ' hζ' ↦ ?_
  have : Nonempty W := ConnectedSpace.toNonempty
  have : ConnectedSpace (overRestrict X' (I.comap f.left).support.compl).left :=
    (Scheme.homeoOfIso (asIso w)).surjective.connectedSpace (Scheme.homeoOfIso (asIso w)).continuous
  let P := (nearbyCyclesVanishNear X' (I.comap f.left) k'
    (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ').inverseImage
      (D(((overRestrictι X' (I.comap f.left).support.compl).left)_!open⟦
        Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧))
  refine P.prop_of_iso ((leftDerivedUpperStarComp _ (inv w) v).app K).symm ?_
  refine prop_of_isBoundedFiniteEllGroupMonodromy_finiteCoefficient (integersResidueField ℓ E.1) ℓ
    P (fun M n hM ↦ ?_) (fun Tr hTr h₁ h₃ ↦ ?_) ?_ _ _ (hW.mapDerivedCategoryUpperStar (inv w))
    (finiteCoefficientDerivedEquivalenceLeftDerivedUpperStarIso _ (inv w)
      (finiteCoefficientDerivedEquivalenceLeftDerivedUpperStarIso _ v e))
  · exact (nearbyCyclesVanishNear X' (I.comap f.left) k' _ ζ').prop_of_iso
      ((((D(((overRestrictι X' (I.comap f.left).support.compl).left)_!open⟦
        Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).commShiftIso n).app M).symm)
      ((nearbyCyclesVanishNear X' (I.comap f.left) k' _ ζ').le_shift n _ hM)
  · exact (nearbyCyclesVanishNear X' (I.comap f.left) k' _ ζ').ext_of_isTriangulatedClosed₂ _
      ((D(((overRestrictι X' (I.comap f.left).support.compl).left)_!open⟦
        Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).map_distinguished _ hTr)
      h₁ h₃
  · have hζ'g := closure_singleton_mem_irreducibleComponents_of_centreMap f I hζ' hζ
    have hI' : I.comap f.left = IdealSheafData.ofIdealTop (Ideal.span {f.left.appTop h}) := by
      rw [hI, IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
    have hh' : f.left.appTop h ≠ 0 := by
      intro h0
      obtain ⟨⟨x, hx⟩⟩ : Nonempty (overRestrict X' (I.comap f.left).support.compl).left :=
        ⟨w (Classical.arbitrary W)⟩
      apply hx
      rw [← IdealSheafData.range_subschemeι, hI', h0,
        IdealSheafData.range_subschemeι_ofIdealTop_span]
      simp
    exact nearbyCyclesVanishNear_lowerShriek_unit_residueField k' hX' hh' hI' ζ' hζ'g E

end AlgebraicGeometry.ProEtale.CondensedRing
