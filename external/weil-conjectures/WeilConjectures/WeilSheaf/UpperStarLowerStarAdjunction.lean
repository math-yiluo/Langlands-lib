/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# The adjunction `φ^* ⊣ φ_*` of Weil sheaves

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes. The pullback and the pushforward of pro-étale
Weil sheaves along `φ` are the pullback and the pushforward along the base change
`φ̄ : X̄ ⟶ Ȳ`, with the Weil structures transported along the Frobenius exchange isomorphisms.
These exchange isomorphisms are mates under `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`), so
the adjunction lifts to pro-étale Weil sheaves, with the unit and the counit of `φ̄^* ⊣ φ̄_*`,
and restricts to Weil sheaves.

The base changes `ī`, `j̄` of morphisms `i`, `j` with complementary ranges again have
complementary ranges (`AlgebraicGeometry.Scheme.Hom.isCompl_range_geometricFiberMap`).

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`: the adjunction
  `φ^* ⊣ φ_*` of pro-étale Weil sheaves.
- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f`: its
  counit is the counit of `φ̄^* ⊣ φ̄_*`; along an open immersion it is invertible.
- `AlgebraicGeometry.WeilSheaf.upperStarLowerStarAdjunction`: `φ^* ⊣ φ_*` on Weil sheaves; its
  unit and counit have the underlying morphisms of `ℓ`-adic sheaves of
  `AlgebraicGeometry.ProEtale.adicUpperStarLowerStarAdjunction`.
- `AlgebraicGeometry.WeilSheaf.isIso_of_isIso_hom_hom_f`: a morphism of Weil sheaves is an
  isomorphism if its underlying morphism of `ℓ`-adic sheaves is.
- `AlgebraicGeometry.WeilSheaf.isIso_upperStarLowerStarAdjunction_counit`: for a quasi-compact
  open immersion `j`, the counit `j^* j_* ⟶ 𝟭` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section GeometricFiber

variable {k : Type u} [Field k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The base change to `k̄` of a closed immersion is a closed immersion. -/
instance [IsClosedImmersion φ] : IsClosedImmersion (Scheme.Hom.geometricFiberMap φ h) :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsClosedImmersion) φ h ‹_›

/-- The range of the base change `φ̄ : X ⟶ Y` of `φ` to `k̄` is the preimage of the range of `φ`
in the geometric fiber `Y`. -/
lemma Scheme.Hom.range_geometricFiberMap :
    Set.range (Scheme.Hom.geometricFiberMap φ h).base =
      g.geometricFiberProj.base ⁻¹' Set.range φ.base := by
  refine (Scheme.Pullback.range_map f (Scheme.specAlgebraicClosure k).hom g
    (Scheme.specAlgebraicClosure k).hom φ (𝟙 _) (𝟙 _) (by simp [h]) (by simp)).trans ?_
  simp [Scheme.Hom.geometricFiberProj]
  rfl

/-- The base changes to `k̄` of morphisms with complementary ranges have complementary
ranges. -/
lemma Scheme.Hom.isCompl_range_geometricFiberMap {Z₀ U₀ : Scheme.{u}}
    {e : Z₀ ⟶ Spec (.of k)} {d : U₀ ⟶ Spec (.of k)} (i : Z₀ ⟶ X₀) (j : U₀ ⟶ X₀)
    (hi : i ≫ f = e) (hj : j ≫ f = d) (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    IsCompl (Set.range (Scheme.Hom.geometricFiberMap i hi).base)
      (Set.range (Scheme.Hom.geometricFiberMap j hj).base) := by
  rw [range_geometricFiberMap, range_geometricFiberMap]
  exact hij.preimage _

end GeometricFiber

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

omit [Fact (ringChar k₀ ≠ l)] in
/-- A pro-étale Weil sheaf is zero if and only if its underlying sheaf is. -/
lemma ProEtaleWeilSheaf.isZero_iff {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (K : ProEtaleWeilSheaf k₀ l X) : IsZero K ↔ IsZero K.carrier :=
  ⟨fun h ↦ (IsoAlgebra.forget _).map_isZero h,
    fun h ↦ (IsZero.iff_id_eq_zero K).2 ((IsoAlgebra.forget _).map_injective (h.eq_of_src _ _))⟩

section Adjunction

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves along a morphism `φ : X ⟶ Y` of
`k₀`-schemes: the adjunction `φ̄^* ⊣ φ̄_*` along the base change `φ̄ : X̄ ⟶ Ȳ`, which is
compatible with the transported Weil structures. -/
noncomputable def ProEtaleWeilSheaf.upperStarLowerStarAdjunction (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.upperStar k₀ l φ ⊣ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  IsoAlgebra.mapOfNatIsoAdjunction
    (ProEtale.adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ (comp_over φ _)))
    _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l φ _)

omit [Fact (ringChar k₀ ≠ l)] in
@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l Y) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).unit.app F).hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).unit.app F.carrier :=
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit.app F).hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).counit.app F.carrier :=
  rfl

/-- Along an open immersion `j`, the counit `j^* j_* F ⟶ F` of pro-étale Weil sheaves is
invertible: so is the counit of `j̄^* ⊣ j̄_*`, and the forgetful functor reflects isomorphisms. -/
instance ProEtaleWeilSheaf.isIso_upperStarLowerStarAdjunction_counit (j : X ⟶ Y)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    IsIso (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  have : IsIso ((IsoAlgebra.forget _).map
      ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).counit.app F)) :=
    inferInstanceAs (IsIso ((ProEtale.adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).counit.app F.carrier))
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

namespace WeilSheaf

/-- A morphism of Weil sheaves is an isomorphism as soon as its underlying morphism of `ℓ`-adic
sheaves is: the forgetful functors reflect isomorphisms. -/
lemma isIso_of_isIso_hom_hom_f {F G : WeilSheaf k₀ l X} (f : F ⟶ G) [IsIso f.hom.hom.f] :
    IsIso f := by
  have : IsIso ((IsoAlgebra.forget _).map f.hom) := inferInstanceAs (IsIso f.hom.hom.f)
  have : IsIso f.hom := isIso_of_reflects_iso _ (IsoAlgebra.forget _)
  exact ⟨⟨ObjectProperty.homMk (inv f.hom), ObjectProperty.hom_ext _ (IsIso.hom_inv_id f.hom),
    ObjectProperty.hom_ext _ (IsIso.inv_hom_id f.hom)⟩⟩

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The adjunction `φ^* ⊣ φ_*` of Weil sheaves: the adjunction `φ̄^* ⊣ φ̄_*` of `ℓ`-adic sheaves
on the geometric fibres, whose unit and counit respect the Weil structures. -/
noncomputable def upperStarLowerStarAdjunction :
    upperStar (k₀ := k₀) (l := l) φ ⊣ lowerStar φ :=
  ObjectProperty.liftFullSubcategoryAdjunction
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ) _ _

/-- The unit `F ⟶ φ_* φ^* F` of Weil sheaves is the unit of `φ̄^* ⊣ φ̄_*`. -/
@[simp]
lemma upperStarLowerStarAdjunction_unit_app_hom_hom_f (F : WeilSheaf k₀ l Y) :
    ((upperStarLowerStarAdjunction φ).unit.app F).hom.hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).unit.app F.obj.carrier :=
  rfl

/-- The counit `φ^* φ_* F ⟶ F` of Weil sheaves is the counit of `φ̄^* ⊣ φ̄_*`. -/
@[simp]
lemma upperStarLowerStarAdjunction_counit_app_hom_hom_f (F : WeilSheaf k₀ l X) :
    ((upperStarLowerStarAdjunction φ).counit.app F).hom.hom.f =
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).counit.app F.obj.carrier :=
  rfl

/-- For a quasi-compact open immersion `j`, the counit `j^* j_* F ⟶ F` of Weil sheaves is an
isomorphism, since the counit of `j̄^* ⊣ j̄_*` is. -/
instance isIso_upperStarLowerStarAdjunction_counit_app {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) :
    IsIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).counit.app F) := by
  have : IsIso ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).counit.app F).hom.hom.f := by
    rw [upperStarLowerStarAdjunction_counit_app_hom_hom_f]
    infer_instance
  exact isIso_of_isIso_hom_hom_f _

/-- For a quasi-compact open immersion `j`, the counit `j^* j_* ⟶ 𝟭` of Weil sheaves is an
isomorphism. -/
instance isIso_upperStarLowerStarAdjunction_counit {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    IsIso (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) j).counit :=
  NatIso.isIso_of_isIso_app _

end WeilSheaf

end Adjunction

end AlgebraicGeometry
