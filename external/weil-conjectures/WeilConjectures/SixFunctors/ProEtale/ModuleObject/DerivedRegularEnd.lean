/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndConstructible

/-!
# The action of a regular endomorphism on the derived category

Let `C` be a closed symmetric monoidal Grothendieck abelian category, `R` a commutative algebra
object and `r` an endomorphism of the regular `R`-module (for instance the multiplication by a
uniformizer `ϖ` of `𝒪_E`). The actions `r_P` on complexes of `R`-modules are natural and descend to
a natural endomorphism `r_K : K ⟶ K` of the identity of `D(Mod_R(C))`
(`CategoryTheory.Mod.derivedRegularEndSMul`).

* `CategoryTheory.Mod.exists_distinguished_derivedRegularEndSMul_derivedExtendScalars`: if
  `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, there is a distinguished triangle
  `K --r_K--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]` whose first morphism is the action of `r`;
* `CategoryTheory.Mod.isIso_derivedRegularEndSMul_of_isZero_derivedExtendScalars`: so `r` acts
  invertibly on `K` as soon as `S ⊗ᴸ_R K = 0`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type*} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ]
  (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R))

/-- The actions `r_P : P ⟶ P` of `r` on complexes of `R`-modules, as a natural endomorphism of the
identity functor. -/
@[simps]
noncomputable def regularEndSMulComplexNatTrans :
    𝟭 (CochainComplex (Mod C R) ℤ) ⟶ 𝟭 (CochainComplex (Mod C R) ℤ) where
  app P := regularEndSMulComplex r P
  naturality P Q g := by
    ext i : 1
    exact (regularEndSMul_naturality r (g.f i)).symm

/-- **The action of `r` on the derived category**: the natural endomorphism `r_K : K ⟶ K` of the
identity of `D(Mod_R(C))` induced by the actions `r_P` on complexes. -/
noncomputable def derivedRegularEndSMul :
    𝟭 (DerivedCategory (Mod C R)) ⟶ 𝟭 (DerivedCategory (Mod C R)) :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Mod C R) (ComplexShape.up ℤ)) DerivedCategory.Q
    DerivedCategory.Q (𝟭 _) (𝟭 _)
    (Functor.whiskerRight (regularEndSMulComplexNatTrans r) DerivedCategory.Q)

/-- On the image of a complex `P`, the action of `r` is the image of `r_P`. -/
lemma derivedRegularEndSMul_app_Q_obj (P : CochainComplex (Mod C R) ℤ) :
    (derivedRegularEndSMul r).app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map (regularEndSMulComplex r P) := by
  rw [derivedRegularEndSMul, Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- Through an isomorphism `Q P ≅ K`, the action of `r` on `K` is the image of `r_P`. -/
lemma derivedRegularEndSMul_app_eq {P : CochainComplex (Mod C R) ℤ}
    {K : DerivedCategory (Mod C R)} (e : DerivedCategory.Q.obj P ≅ K) :
    (derivedRegularEndSMul r).app K =
      e.inv ≫ DerivedCategory.Q.map (regularEndSMulComplex r P) ≫ e.hom := by
  rw [← derivedRegularEndSMul_app_Q_obj]
  have := (derivedRegularEndSMul r).naturality e.hom
  simp only [Functor.id_map, Functor.id_obj] at this
  rw [← this, Iso.inv_hom_id_assoc]

variable {r} [Abelian.HasFunctorialFlatResolution C]

/-- **The reduction triangle modulo `r`, with its first morphism**: if
`0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, then for every `K ∈ D(Mod_R(C))` there is a
distinguished triangle `K --r_K--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]`, the first map being the action of `r` on
the derived category, and the derived extension of scalars `S ⊗ᴸ_R K` being regarded as a complex
of `R`-modules:
```
K --r_K--> K --g--> S ⊗ᴸ_R K --h--> K[1]
```
-/
theorem exists_distinguished_derivedRegularEndSMul_derivedExtendScalars (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (K : DerivedCategory (Mod C R)) :
    ∃ (g : K ⟶ (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K))
      (h : (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) ⟶
        K⟦(1 : ℤ)⟧),
      Triangle.mk ((derivedRegularEndSMul r).app K) g h ∈
        distTriang (DerivedCategory (Mod C R)) := by
  have := hφ.mono_f
  obtain ⟨P, π, _, hflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have hS := shortExact_regularEndSMulComplex w hφ P
    (fun n ↦ mono_regularEndSMul_of_flat (P.X n) (hflat n))
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let e₁ : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let e₃ : DerivedCategory.Q.obj
      (((extendScalars φ ⋙ comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) :=
    ((comap φ).mapDerivedCategoryFactors.app
        (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso
        ((DerivedCategory.quotientCompQhIso (Mod C S)).app
            (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso
        (asIso ((extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P))).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso ((extendScalars φ).leftDerivedFunctor.mapIso
        ((DerivedCategory.quotientCompQhIso (Mod C R)).app P ≪≫ e₁))
  refine ⟨e₁.inv ≫ DerivedCategory.Q.map (extendUnitComplexHom φ P) ≫ e₃.hom,
    e₃.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e₁.hom⟦(1 : ℤ)⟧', ?_⟩
  rw [derivedRegularEndSMul_app_eq r e₁]
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ e₁ e₁ e₃ ?_ ?_ ?_).symm
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES]

/-- If `0 ⟶ R --r--> R --φ--> S ⟶ 0` is short exact, `r` acts invertibly on every complex `K`
whose derived extension of scalars `S ⊗ᴸ_R K` vanishes. -/
theorem isIso_derivedRegularEndSMul_of_isZero_derivedExtendScalars (w : r.hom ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) {K : DerivedCategory (Mod C R)}
    (hK : IsZero ((extendScalars φ).leftDerivedFunctor.obj K)) :
    IsIso ((derivedRegularEndSMul r).app K) := by
  obtain ⟨g, h, hT⟩ := exists_distinguished_derivedRegularEndSMul_derivedExtendScalars w hφ K
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 ((comap φ).mapDerivedCategory.map_isZero hK)

end CategoryTheory.Mod
