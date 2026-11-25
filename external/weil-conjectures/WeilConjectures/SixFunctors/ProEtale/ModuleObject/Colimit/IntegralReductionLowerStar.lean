/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionOpenLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionRestrictConstructibleProof

/-!
# The pushforward on bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes

Let `ℓ` be a prime invertible in the field `k`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring
of integers `𝒪_E`, and `n : ℕ`. This file proves **Deligne's finiteness theorem** for `Rf_*` with
coefficients in `𝒪_E ⧸ ℓⁿ` from the one with coefficients in `𝒪_E`
(`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj`)
(`ProEtale.CondensedRing.IntegersModPowRingObj.boundedConstructible_rightDerivedLowerStar_obj`),
and restricts `Rf_*` to bounded constructible complexes, mirroring the `ℓ`-adic coefficient rings
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:

* `IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n f`, compatible with the inclusions
  (`IntegersModPowRingObj.boundedConstructibleLowerStarCompatibility`);
* the adjunction `Lf^* ⊣ Rf_*`
  (`IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction`);
* the composition isomorphism (`IntegersModPowRingObj.boundedConstructibleLowerStarComp`).

The finiteness theorem is deduced by restriction of scalars `Res` along
`𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X`: for `M ∈ Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧`, `Res M` is bounded constructible over
`𝒪_E` (`ProEtale.CondensedRing.restrictScalarsIntegersModPowBoundedConstructible`), `Res` commutes
with `Rf_*` (`ProEtale.CondensedRing.rightDerivedLowerStarComapIso`), and a complex whose
restriction of scalars is bounded constructible is bounded constructible
(`ProEtale.boundedConstructible_of_boundedConstructible_comap_integersModPowReduction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- **Bounded constructibility descends along the restriction of scalars** along
`𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X`: an `𝒪_E ⧸ ℓⁿ`-complex whose restriction of scalars is a bounded
constructible `𝒪_E`-complex is bounded constructible. The restriction of scalars is exact and
reflects zero objects, and constructibility descends along it
(`ProEtale.IsConstructibleModuleObject.of_comap_of_shortExact`). -/
lemma boundedConstructible_of_boundedConstructible_comap_integersModPowReduction
    {X : Scheme.{u}} {M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X))}
    (hM : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      (D(Mod.comap (integersModPowReduction X ℓ E n)).obj M)) :
    boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) M := by
  have hiso (i : ℤ) :=
    ((Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategoryHomologyFunctorIso i).app M
  rw [mem_boundedConstructible_iff] at hM ⊢
  obtain ⟨⟨a, b, hab⟩, hc⟩ := hM
  exact ⟨⟨a, b, fun i hi ↦ Mod.isZero_of_isZero_comap _ ((hab i hi).of_iso (hiso i))⟩,
    fun i ↦ IsConstructibleModuleObject.of_comap_of_shortExact _ _
      (shortExact_integersModPowReduction X ℓ E n) ((hc i).of_iso (hiso i).symm)⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegersModPowRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **Deligne's finiteness theorem** for `Rf_*` with coefficients in `𝒪_E ⧸ ℓⁿ`: the derived
pushforward along a morphism of separated `k`-schemes of finite type carries bounded
constructible `𝒪_E ⧸ ℓⁿ`-complexes to bounded constructible complexes. It follows from the one
for `𝒪_E` (`PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj`), as the
restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` preserves and reflects bounded constructibility and
commutes with `Rf_*`. -/
lemma boundedConstructible_rightDerivedLowerStar_obj
    (K : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y.left)
      ((R((f.left)_*⟦Profinite.integersModPowRingObj ℓ E n⟧)).obj K.obj) := by
  have h := PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f
    ⟨_, restrictScalarsIntegersModPowBoundedConstructible ℓ E n X.left K.obj K.property⟩
  exact boundedConstructible_of_boundedConstructible_comap_integersModPowReduction ℓ E n
    ((boundedConstructible _).prop_of_iso
      ((rightDerivedLowerStarComapIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
        f.left).app K.obj).symm h)

/-- The derived pushforward `Rf_* : Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ ⥤ Dᵇc(Y)⟦𝒪_E ⧸ ℓⁿ⟧` on bounded
constructible complexes: the restriction of `R((f)_*⟦𝒪_E ⧸ ℓⁿ⟧)`. -/
noncomputable def boundedConstructibleLowerStar :
    Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤
      Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.integersModPowRingObj ℓ E n⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E n f K

/-- The restricted derived pushforward is compatible with the inclusions
(`𝒪_E ⧸ ℓⁿ`-coefficient). -/
noncomputable def boundedConstructibleLowerStarCompatibility :
    boundedConstructibleLowerStar ℓ E n f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Profinite.integersModPowRingObj ℓ E n⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The derived adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes
(`𝒪_E ⧸ ℓⁿ`-coefficient): the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` along the fully faithful
inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunction :
    boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ f ⊣
      boundedConstructibleLowerStar ℓ E n f :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.integersModPowRingObj ℓ E n) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.integersModPowRingObj ℓ E n) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ E n f).symm

/-- The derived pullback `Lf^*` on bounded constructible complexes is a left adjoint
(`𝒪_E ⧸ ℓⁿ`-coefficient). -/
instance isLeftAdjoint_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ f).IsLeftAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f).isLeftAdjoint

/-- The derived pushforward `Rf_*` on bounded constructible complexes is a right adjoint
(`𝒪_E ⧸ ℓⁿ`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ E n f).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f).isRightAdjoint

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` on bounded constructible complexes
(`𝒪_E ⧸ ℓⁿ`-coefficient): the conjugate of `boundedConstructibleUpperStarComp`. -/
noncomputable def boundedConstructibleLowerStarComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    boundedConstructibleLowerStar ℓ E n f ⋙ boundedConstructibleLowerStar ℓ E n g ≅
      boundedConstructibleLowerStar ℓ E n (f ≫ g) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction ℓ E n (f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E n g).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f))
    (boundedConstructibleUpperStarComp (Profinite.integersModPowRingObj ℓ E n) ℓ f g).symm).symm

/-- For an open immersion `j`, the counit `Lj^* Rj_* ⟶ 𝟭` on bounded constructible complexes is
an isomorphism (`𝒪_E ⧸ ℓⁿ`-coefficient). -/
instance isIso_counit_boundedConstructibleUpperStarLowerStarAdjunction_of_isOpenImmersion
    {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ E n j).counit :=
  isIso_counit_of_isOpenImmersion_of_lowerStarCompatibility _ j.left _
    (boundedConstructibleLowerStarCompatibility ℓ E n j)

/-- The derived pushforward on bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes commutes with the
shifts. -/
noncomputable instance commShift_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ E n f).CommShift ℤ := by
  delta boundedConstructibleLowerStar
  infer_instance

instance commShift_boundedConstructibleLowerStarCompatibility_hom :
    NatTrans.CommShift (boundedConstructibleLowerStarCompatibility ℓ E n f).hom ℤ := by
  unfold boundedConstructibleLowerStarCompatibility boundedConstructibleLowerStar
  infer_instance

/-- The adjunction `Lf^* ⊣ Rf_*` on bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes commutes with the
shifts. -/
instance commShift_boundedConstructibleUpperStarLowerStarAdjunction :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ E n f).CommShift ℤ :=
  Adjunction.commShift_restrictFullyFaithful _ _ _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing.IntegersModPowRingObj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The derived pushforward on bounded constructible `𝒪_E`-complexes commutes with the shifts. -/
noncomputable instance commShift_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ E f).CommShift ℤ := by
  delta boundedConstructibleLowerStar
  infer_instance

/-- The derived pushforward along a proper morphism on bounded constructible `𝒪_E`-complexes
commutes with the shifts. -/
noncomputable instance commShift_boundedConstructibleLowerStarOfIsProper [IsProper f.left] :
    (boundedConstructibleLowerStarOfIsProper ℓ E f).CommShift ℤ := by
  delta boundedConstructibleLowerStarOfIsProper
  infer_instance

instance commShift_boundedConstructibleLowerStarCompatibility_hom :
    NatTrans.CommShift (boundedConstructibleLowerStarCompatibility ℓ E f).hom ℤ := by
  unfold boundedConstructibleLowerStarCompatibility boundedConstructibleLowerStar
  infer_instance

/-- The adjunction `Lf^* ⊣ Rf_*` on bounded constructible `𝒪_E`-complexes commutes with the
shifts. -/
instance commShift_boundedConstructibleUpperStarLowerStarAdjunction :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).CommShift ℤ :=
  Adjunction.commShift_restrictFullyFaithful _ _ _ _ _

/-- The derived pushforward on bounded constructible `𝒪_E`-complexes is triangulated. -/
instance isTriangulated_boundedConstructibleLowerStar :
    (boundedConstructibleLowerStar ℓ E f).IsTriangulated := by
  delta boundedConstructibleLowerStar
  infer_instance

/-- The derived pullback on bounded constructible `𝒪_E`-complexes is triangulated. -/
instance isTriangulated_boundedConstructibleUpperStar :
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).IsTriangulated := by
  delta boundedConstructibleUpperStar
  infer_instance

/-- The extension by zero on bounded constructible `𝒪_E`-complexes is triangulated. -/
instance isTriangulated_boundedConstructibleOpenImmersionLowerShriek {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (j : U ⟶ X)
    [IsOpenImmersion j.left] :
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ
      j).IsTriangulated := by
  delta boundedConstructibleOpenImmersionLowerShriek
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
