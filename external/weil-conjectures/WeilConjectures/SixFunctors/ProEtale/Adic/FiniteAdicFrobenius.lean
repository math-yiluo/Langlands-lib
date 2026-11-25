/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ContinuousSheafPullback
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.ConstantRingEndomorphisms
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicEtaleEquiv
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Pullback along an automorphism and the comparison `Hⁿ(S_proét, ℤ/ℓᵐ) ≅ Extⁿ_Λ(Λ_S, Λ_S)`

Let `S` be a connected quasi-compact quasi-separated scheme, `e : S ≅ S` an automorphism (e.g.
the geometric Galois Frobenius of `X̄ = X ×_{k₀} k̄`) and `Λ = ℤ/ℓᵐ`. The comparison
`Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)` (`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`)
intertwines the pullback `e^*` of pro-étale cohomology
(`AlgebraicGeometry.ProEtale.finiteAdicHPullback`) with the pullback of `Ext`-classes along the
exact functor `e^*` on étale sheaves of `Λ`-modules, read through the identification
`e^* Λ_S ≅ Λ_S` underlying `Le^* Λ_S ≅ Λ_S`
(`AlgebraicGeometry.ProEtale.finiteAdicHPullback_extAddEquivFiniteAdicH`).

## Proof

`ν^* ∘ forget` commutes with the pullbacks up to a natural isomorphism, so both sides differ only
by morphisms on the two sides of the classes. As every endomorphism of `Λ_S` is a scalar and
`ν^* ∘ forget` is full on these, the two sides differ by an integer `c` independent of the degree
(`CategoryTheory.Abelian.Ext.exists_mk₀CompMk₀_mapExactFunctor_eq_zsmul`). In degree `0` both
pullbacks fix the class of the constant section `1`, whose order is `ℓᵐ`, so `c ≡ 1 mod ℓᵐ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

/-! Without this, `ModuleCat (ULift (ZMod (l ^ m)))` elaborates with the ring structure
`ULift.ring`, while the constructions on sheaves of modules over a commutative ring use
`CommRing.toRing`; the kernel then has to unfold the sheaf categories to compare the two. -/
attribute [local instance 2000] CommRing.toRing

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance high] hasExt_sheafEtaleModuleCatZMod hasExt_sheafEtaleAddCommGrpCat
  hasExt_sheafProEtAddCommGrpCat

/-! The constructions on sheaves of modules over a commutative ring `Λ` (such as
`AlgebraicGeometry.Etale.upperStarConstantRingIso`) sheafify through `HasSheafify`; for
`Λ = ULift (ZMod (l ^ m))`, instance synthesis would otherwise use the concrete sheafification
`CategoryTheory.sheafToPresheaf_isRightAdjoint` in `Sheaf.constantRing`, and the kernel would
have to unfold the sheaf categories to compare the two. -/
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

variable (l : ℕ) [Fact l.Prime] (m : ℕ) {S : Scheme.{u}} (e : S ≅ S)

omit [Fact l.Prime] in
lemma surjective_intCast_ulift_zmod :
    Function.Surjective (Int.cast : ℤ → ULift.{u + 1} (ZMod (l ^ m))) := fun x ↦
  ⟨(ZMod.intCast_surjective x.down).choose, ULift.ext (by
    simpa using (ZMod.intCast_surjective x.down).choose_spec)⟩

/-- `ν^* ∘ forget` commutes with the pullbacks along `e`, the pro-étale one being the pushforward
along `e⁻¹`. -/
noncomputable def forgetComparisonUpperStarLowerStarIso :
    forgetComparisonUpperStar l m S ⋙ ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv ≅
      Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m)))) e.hom ⋙
        forgetComparisonUpperStar l m S :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv AddCommGrpCat.{u + 1} e).symm ≪≫
        comparisonUpperStarUpperStarIso AddCommGrpCat.{u + 1} e.hom) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (Etale.upperStarForget₂ (ULift.{u + 1} (ZMod (l ^ m))) e.hom)) _ ≪≫
    Functor.associator _ _ _

variable (S) in
/-- The class of the constant function `1` in `H⁰(S_proét, ℤ_ℓ/ℓᵐ)`. -/
noncomputable def finiteAdicHOne : FiniteAdicH S l m 0 :=
  Sheaf.H.map (continuousSheafMap S
    ⟨((zmodAddEquivQuotientPowOpenAddSubgroup l m).toAddMonoidHom.comp
      (Int.castAddHom (ZMod (l ^ m)))), continuous_of_discreteTopology⟩) 0
    (Ext.mk₀ (constantSheafIsoContinuousSheaf S ℤ).hom)

/-- The pullback fixes the class of the constant function `1`. -/
lemma finiteAdicHPullback_finiteAdicHOne :
    finiteAdicHPullback e l m 0 (finiteAdicHOne l m S) = finiteAdicHOne l m S := by
  refine (continuousSheafHPullback_map e _ 0 _).trans (congrArg _ ?_)
  rw [continuousSheafHPullback_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀]
  congr 1
  simp [constantIntIsoLowerStar]

/-- `ℓᵐ` kills `Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)`, as an integer multiple. -/
lemma zsmul_pow_finiteAdicH (n : ℕ) (z : FiniteAdicH S l m n) : ((l : ℤ) ^ m) • z = 0 := by
  rw [← Int.cast_smul_eq_zsmul ℤ_[l]]
  push_cast
  exact pow_smul_finiteAdicH S l m n z

variable (S) in
/-- The class of the constant function `1` has order `ℓᵐ`. -/
lemma dvd_of_zsmul_finiteAdicHOne_eq_zero [Nonempty S] (k : ℤ)
    (hk : k • finiteAdicHOne l m S = 0) : (l : ℤ) ^ m ∣ k := by
  let A := ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l])
  let φ : ContinuousAddMonoidHom ℤ A :=
    ⟨((zmodAddEquivQuotientPowOpenAddSubgroup l m).toAddMonoidHom.comp
      (Int.castAddHom (ZMod (l ^ m)))), continuous_of_discreteTopology⟩
  let f := (constantSheafIsoContinuousSheaf S ℤ).hom ≫ continuousSheafMap S φ
  have hf : k • f = 0 := by
    apply (Ext.mk₀_bijective _ _).1
    rw [Ext.mk₀_zsmul, Ext.mk₀_zero, ← Ext.mk₀_comp_mk₀]
    exact hk
  let T := Scheme.ProEt.mk (𝟙 S)
  let F := sheafToPresheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj (Opposite.op T)
  have h2 : ((toSheafify (ProEt.topology S) _).app (Opposite.op T) ≫ F.map (k • f)).hom
      (ULift.up 1) = 0 := by
    rw [hf, Functor.map_zero, Limits.comp_zero]
    rfl
  rw [Functor.map_zsmul, Preadditive.comp_zsmul, AddCommGrpCat.hom_zsmul] at h2
  have h3 : (toSheafify (ProEt.topology S) _).app (Opposite.op T) ≫ F.map f =
      (constToContinuousSheaf S ℤ ≫ (continuousSheafMap S φ).hom).app (Opposite.op T) := by
    rw [← toSheafify_constantSheafToContinuousSheaf]
    rfl
  rw [h3] at h2
  obtain ⟨s⟩ : Nonempty T.left := ‹Nonempty S›
  have e1 : ((constToContinuousSheaf S ℤ ≫ (continuousSheafMap S φ).hom).app
      (Opposite.op T)).hom (ULift.up 1) = ULift.up (ContinuousMap.const _ (φ 1)) := rfl
  rw [AddMonoidHom.zsmul_apply] at h2
  erw [e1] at h2
  have h4 : k • φ 1 = 0 :=
    congrArg (fun g : ULift.{u + 1} C(T.left, A) ↦ g.down s) h2
  have h5 : (k : ZMod (l ^ m)) = 0 := by
    apply (zmodAddEquivQuotientPowOpenAddSubgroup l m).injective
    rw [map_zero, ← h4, ← zsmul_one, map_zsmul]
    exact congrArg (fun x : ZMod (l ^ m) ↦ k • zmodAddEquivQuotientPowOpenAddSubgroup l m x)
      Int.cast_one.symm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h5
  exact_mod_cast h5

variable [CompactSpace S] [QuasiSeparatedSpace S]

omit [Fact l.Prime] in
variable (S) in
/-- Every morphism `ℤ ⟶ ν^* Λ` of pro-étale sheaves is `u ≫ ν^* f` for an endomorphism `f` of
`Λ_S`, `u` the class of `1`. -/
lemma exists_eq_forgetComparisonUpperStarUnit_comp
    (h : (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ (forgetComparisonUpperStar l m S).obj
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))) :
    ∃ f, h = forgetComparisonUpperStarUnit l m S ≫ (forgetComparisonUpperStar l m S).map f := by
  obtain ⟨w, hw⟩ := (bijective_cohomologyComparison S
    ((Etale.sheafForget₂ (ULift.{u + 1} (ZMod (l ^ m))) S).obj
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))))
        0).2 (Ext.mk₀ h)
  obtain ⟨y, rfl⟩ :=
    (Etale.bijective_mapExtComp_constantIntToRing (ULift.{u + 1} (ZMod (l ^ m))) S _ 0).2 w
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  refine ⟨f, (Ext.mk₀_bijective _ _).1 ?_⟩
  rw [← hw, cohomologyComparison_apply, Functor.mapExtComp_apply, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, forgetComparisonUpperStarUnit,
    Functor.map_comp, Category.assoc]
  rfl

omit [Fact l.Prime] [CompactSpace S] [QuasiSeparatedSpace S] in
variable (S) in
/-- `ν^* ∘ forget` is full on étale sheaves of `ℤ/ℓᵐ`-modules. -/
lemma exists_forgetComparisonUpperStar_map_eq
    {M N : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m))))}
    (h : (forgetComparisonUpperStar l m S).obj M ⟶ (forgetComparisonUpperStar l m S).obj N) :
    ∃ f, h = (forgetComparisonUpperStar l m S).map f := by
  obtain ⟨h', rfl⟩ := (comparisonUpperStar AddCommGrpCat.{u + 1} S).map_surjective h
  obtain ⟨f, rfl⟩ := Etale.exists_sheafForget₂_map_eq (surjective_intCast_ulift_zmod l m) h'
  exact ⟨f, rfl⟩

/-- The pullback of `Ext`-classes along `e^*`, read through `e^* Λ_S ≅ Λ_S`. -/
noncomputable def extPullback (n : ℕ)
    (y : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) n) :
    Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) n :=
  Ext.mk₀CompMk₀ (Etale.upperStarConstantRingIso _ e.hom).inv
    (y.mapExactFunctor (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m))))
      e.hom)) (Etale.upperStarConstantRingIso _ e.hom).hom

omit [CompactSpace S] [QuasiSeparatedSpace S] in
lemma finiteAdicHPullback_eq_mk₀CompMk₀ (n : ℕ) (x : FiniteAdicH S l m n) :
    finiteAdicHPullback e l m n x =
      Ext.mk₀CompMk₀ (constantIntIsoLowerStar e).hom
        (x.mapExactFunctor (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv))
        (continuousSheafIsoLowerStar e _).inv :=
  Ext.mk₀_comp_comp_mk₀ _ _ _

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- Both pullbacks agree up to explicit morphisms on the two sides of the classes. -/
lemma mk₀CompMk₀_mapExactFunctor_lowerStar_eq (n : ℕ)
    (y : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) n) :
    Ext.mk₀CompMk₀ (constantIntIsoLowerStar e).hom
        ((Ext.mk₀CompMk₀ (forgetComparisonUpperStarUnit l m S)
          (y.mapExactFunctor (forgetComparisonUpperStar l m S))
          (forgetComparisonUpperStarConstantRingIso l m S).hom).mapExactFunctor
            (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv))
        (continuousSheafIsoLowerStar e _).inv =
      Ext.mk₀CompMk₀ ((constantIntIsoLowerStar e).hom ≫
          (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv).map
            (forgetComparisonUpperStarUnit l m S) ≫
          (forgetComparisonUpperStarLowerStarIso l m e).hom.app _ ≫
          (forgetComparisonUpperStar l m S).map (Etale.upperStarConstantRingIso _ e.hom).hom)
        ((Ext.mk₀CompMk₀ (Etale.upperStarConstantRingIso _ e.hom).inv
          (y.mapExactFunctor (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m))))
            e.hom)) (Etale.upperStarConstantRingIso _ e.hom).hom).mapExactFunctor
              (forgetComparisonUpperStar l m S))
        ((forgetComparisonUpperStar l m S).map (Etale.upperStarConstantRingIso _ e.hom).inv ≫
          (forgetComparisonUpperStarLowerStarIso l m e).inv.app _ ≫
          (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv).map
            (forgetComparisonUpperStarConstantRingIso l m S).hom ≫
          (continuousSheafIsoLowerStar e _).inv) :=
  Ext.mapExactFunctor_mk₀CompMk₀_of_iso _ _ _ _ _ _ _ _ _ y

/-- The two pullbacks differ by an integer multiple, independent of the degree. -/
lemma exists_finiteAdicHPullback_extAddEquivFiniteAdicH_eq_zsmul [ConnectedSpace S] :
    ∃ c : ℤ, ∀ (n : ℕ) (y : Ext (Sheaf.constantRing S.smallEtaleTopology
        (ULift.{u + 1} (ZMod (l ^ m)))) (Sheaf.constantRing S.smallEtaleTopology
          (ULift.{u + 1} (ZMod (l ^ m)))) n),
      finiteAdicHPullback e l m n (extAddEquivFiniteAdicH l m S n y) =
        c • extAddEquivFiniteAdicH l m S n (extPullback l m e n y) := by
  obtain ⟨c, hc⟩ := Ext.exists_mk₀CompMk₀_mapExactFunctor_eq_zsmul
    (forgetComparisonUpperStar l m S) (forgetComparisonUpperStarUnit l m S)
    (forgetComparisonUpperStarConstantRingIso l m S)
    ((constantIntIsoLowerStar e).hom ≫
      (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv).map
        (forgetComparisonUpperStarUnit l m S) ≫
      (forgetComparisonUpperStarLowerStarIso l m e).hom.app _ ≫
      (forgetComparisonUpperStar l m S).map (Etale.upperStarConstantRingIso _ e.hom).hom)
    ((forgetComparisonUpperStar l m S).map (Etale.upperStarConstantRingIso _ e.hom).inv ≫
      (forgetComparisonUpperStarLowerStarIso l m e).inv.app _ ≫
      (ProEtale.lowerStar AddCommGrpCat.{u + 1} e.inv).map
        (forgetComparisonUpperStarConstantRingIso l m S).hom ≫
      (continuousSheafIsoLowerStar e _).inv)
    (Etale.exists_eq_zsmul_id_constantRing (surjective_intCast_ulift_zmod l m) S)
    (exists_eq_forgetComparisonUpperStarUnit_comp l m S)
    (exists_forgetComparisonUpperStar_map_eq l m S)
  refine ⟨c, fun n y ↦ ?_⟩
  rw [finiteAdicHPullback_eq_mk₀CompMk₀, extAddEquivFiniteAdicH_apply,
    mk₀CompMk₀_mapExactFunctor_lowerStar_eq, hc, extAddEquivFiniteAdicH_apply, extPullback]

omit [Fact l.Prime] [CompactSpace S] [QuasiSeparatedSpace S] in
lemma extPullback_mk₀_id :
    extPullback l m e 0 (Ext.mk₀ (𝟙 (Sheaf.constantRing S.smallEtaleTopology
      (ULift.{u + 1} (ZMod (l ^ m)))))) = Ext.mk₀ (𝟙 _) := by
  rw [extPullback, Ext.mapExactFunctor_mk₀, CategoryTheory.Functor.map_id, Ext.mk₀CompMk₀,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Category.id_comp, Iso.inv_hom_id]

/-- The class of `1` is an integer multiple of the image of the identity of `Λ_S`. -/
lemma exists_finiteAdicHOne_eq_zsmul [ConnectedSpace S] :
    ∃ j : ℤ, finiteAdicHOne l m S = j • extAddEquivFiniteAdicH l m S 0
      (Ext.mk₀ (𝟙 (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))))) := by
  obtain ⟨y₀, hy₀⟩ := (extAddEquivFiniteAdicH l m S 0).surjective (finiteAdicHOne l m S)
  obtain ⟨f₀, rfl⟩ := (Ext.mk₀_bijective _ _).2 y₀
  obtain ⟨j, rfl⟩ :=
    Etale.exists_eq_zsmul_id_constantRing (surjective_intCast_ulift_zmod l m) S f₀
  exact ⟨j, by rw [← hy₀, Ext.mk₀_zsmul, map_zsmul]⟩

omit [Fact l.Prime] in
/-- If an additive endomorphism `F` fixes `o = j • x` and `F x = c • x`, then `(c - 1) • o = 0`. -/
lemma _root_.AddMonoidHom.zsmul_sub_one_eq_zero {M : Type*} [AddCommGroup M] (F : M →+ M)
    {o x : M} {c j : ℤ} (ho : o = j • x) (hFo : F o = o) (hFx : F x = c • x) :
    (c - 1) • o = 0 := by
  subst ho
  rw [map_zsmul, hFx, smul_comm] at hFo
  rw [sub_zsmul, one_zsmul, hFo, add_neg_cancel]

omit [Fact l.Prime] in
lemma _root_.zsmul_eq_self_of_sub_one_zsmul_eq_zero {M : Type*} [AddCommGroup M] {c : ℤ}
    {z : M} (h : (c - 1) • z = 0) : c • z = z := by
  rw [← sub_eq_zero, ← h, sub_zsmul, one_zsmul, sub_eq_add_neg]

/-- **The comparison `Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)` commutes with pullback along an
automorphism `e` of a connected scheme `S`.** On the left, a class `y` is pushed forward along the
exact functor `e^*` on étale sheaves of `Λ`-modules and read through the isomorphism
`e^* Λ_S ≅ Λ_S` underlying `Le^* Λ_S ≅ Λ_S`; on the right, `e^*` is the pullback of pro-étale
cohomology. -/
theorem finiteAdicHPullback_extAddEquivFiniteAdicH [ConnectedSpace S] (n : ℕ)
    (y : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) n) :
    finiteAdicHPullback e l m n (extAddEquivFiniteAdicH l m S n y) =
      extAddEquivFiniteAdicH l m S n (extPullback l m e n y) := by
  obtain ⟨c, key⟩ := exists_finiteAdicHPullback_extAddEquivFiniteAdicH_eq_zsmul l m e
  obtain ⟨j, hj⟩ := exists_finiteAdicHOne_eq_zsmul l m (S := S)
  have h1 := key 0 (Ext.mk₀ (𝟙 _))
  rw [extPullback_mk₀_id] at h1
  have hco := (finiteAdicHPullback e l m 0).toAddMonoidHom.zsmul_sub_one_eq_zero hj
    (finiteAdicHPullback_finiteAdicHOne l m e) h1
  obtain ⟨d, hd⟩ := dvd_of_zsmul_finiteAdicHOne_eq_zero l m S (c - 1) hco
  rw [key]
  refine zsmul_eq_self_of_sub_one_zsmul_eq_zero ?_
  rw [hd, mul_comm, mul_zsmul, zsmul_pow_finiteAdicH, zsmul_zero]

end AlgebraicGeometry.ProEtale
