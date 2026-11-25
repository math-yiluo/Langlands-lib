/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelSections
public import WeilConjectures.WeilObject.Sheaf.EndTensorUnitTrace
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelPointTrace
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

/-!
# The trace of the Galois action at a separably closed point in the two models

The categorical trace of the Galois action `x^* M ⟶ σ^* x^* M ≅ x^* M` on a module object,
followed by a scalar `c`, is `c` times the trace of the Galois action on the global sections
`Γ(x^* H)` of the corresponding ℓ-adic sheaf.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The pullback commutes with the multiplication by a scalar. -/
lemma adicUpperStar_map_smul {X Z : Scheme.{u}} (g : Z ⟶ X) (c : ULift.{u + 1} (PadicAlgCl l))
    (M : AdicSheaf l X) : (g)^*ᵃ[l].map (AdicSheaf.smul c M) = AdicSheaf.smul c ((g)^*ᵃ[l].obj
        M) :=
  Mod.hom_ext _ _ (by
    rw [adicUpperStar_map_hom, AdicSheaf.smul_hom, AdicSheaf.smul_hom, Functor.map_smul,
      CategoryTheory.Functor.map_id]
    rfl)

/-- The Galois action on the global sections of the pullback of an `ℓ`-adic sheaf along `x` with
`σ ≫ x = x`: `Γ(x^* H) ⟶ Γ(σ^* x^* H) ≅ Γ((σ ≫ x)^* H) = Γ(x^* H)`. -/
noncomputable def galoisGlobalSections {S X : Scheme.{u}} (σ : S ⟶ S) (x : S ⟶ X)
    (h : σ ≫ x = x) (H : AdicSheaf l X) :
    (Sheaf.Γ _ _).obj ((x)^*ᵃ[l].obj H).X ⟶ (Sheaf.Γ _ _).obj ((x)^*ᵃ[l].obj H).X :=
  (globalSectionsToUpperStar _ σ).app ((x)^*ᵃ[l].obj H).X ≫
    (Sheaf.Γ _ _).map ((adicUpperStarComp l σ x).inv.app H ≫
      (adicUpperStarCongr l h).hom.app H).hom

/-- The Galois action on global sections is the pullback of morphisms out of `ℚ̄_ℓ`. -/
lemma galoisGlobalSections_globalSectionOfModHom {S X : Scheme.{u}} (σ : S ⟶ S) (x : S ⟶ X)
    (h : σ ≫ x = x) (H : AdicSheaf l X) (v : AdicSheaf.unit l S ⟶ (x)^*ᵃ[l].obj H) :
    (galoisGlobalSections σ x h H).hom (globalSectionOfModHom v) =
      globalSectionOfModHom (adicUpperStarSectionMap σ x h H v) := by
  rw [galoisGlobalSections, ModuleCat.hom_comp, LinearMap.comp_apply,
    globalSectionsToUpperStar_globalSectionOfModHom, adicUpperStarSectionMap,
    ← Category.assoc,
        globalSectionOfModHom_comp ((adicUpperStarUnitIso l σ).inv ≫ (σ)^*ᵃ[l].map v)]
  rfl

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.MonoidalCategory.UnitBasis

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] {X Y : C} {ι : Type*}
  [Fintype ι] [DecidableEq ι]

/-- A unit basis transported along an isomorphism. -/
@[simps]
noncomputable def ofIsoBasis (b : UnitBasis X ι) (e : Y ≅ X) : UnitBasis Y ι where
  incl i := b.incl i ≫ e.inv
  proj i := e.hom ≫ b.proj i
  incl_proj i j := by rw [Category.assoc, e.inv_hom_id_assoc, b.incl_proj]
  total := by
    simp only [Category.assoc, ← Preadditive.comp_sum]
    simp only [← Category.assoc, ← Preadditive.sum_comp]
    rw [b.total, Category.comp_id, e.hom_inv_id]

end CategoryTheory.MonoidalCategory.UnitBasis

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

lemma adicSheafEquivCondensedModTensorUnitIso_eq (X : Scheme.{u}) :
    adicSheafEquivCondensedModTensorUnitIso l X = adicSheafEquivCondensedModUnitIso l X :=
  Iso.ext (Mod.hom_ext _ _ (by
    rw [adicSheafEquivCondensedModTensorUnitIso_hom_hom,
        adicSheafEquivCondensedModUnitIso_hom_hom]))

/-- The image of the multiplication by `c` on `ℚ̄_ℓ` at a separably closed point is the scalar
`c` on the unit. -/
lemma adicSheafEquivCondensedModTensorUnitIso_inv_comp_map_smul_comp_hom (Ω : Type u)
    [Field Ω] [IsSepClosed Ω] (c : PadicAlgCl l) :
    (adicSheafEquivCondensedModTensorUnitIso l (Spec (.of Ω))).inv ≫
        (adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.map
          (AdicSheaf.smul (ULift.up c) (AdicSheaf.unit l (Spec (.of Ω)))) ≫
        (adicSheafEquivCondensedModTensorUnitIso l (Spec (.of Ω))).hom =
      (CondensedRing.scalarEndRingHom l (Spec (.of Ω)) c).asHom := by
  apply End.homEquiv.symm.injective
  dsimp only [End.homEquiv, Equiv.symm, Equiv.coe_fn_mk]
  apply (CondensedRing.endTensorUnitRingEquiv l Ω).injective
  rw [adicSheafEquivCondensedModTensorUnitIso_eq,
    endTensorUnitRingEquiv_adicSheafEquivCondensedMod_map_smul,
    CondensedRing.endTensorUnitRingEquiv_scalarEndRingHom]

lemma condensedSectionOfAdicSection_smul_comp (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    {T : Scheme.{u}} (x : Spec (.of Ω) ⟶ T) (H : AdicSheaf l T) (c : PadicAlgCl l)
    (v : AdicSheaf.unit l (Spec (.of Ω)) ⟶ (x)^*ᵃ[l].obj H) :
    condensedSectionOfAdicSection x H (AdicSheaf.smul (ULift.up c) _ ≫ v) =
      (CondensedRing.scalarEndRingHom l (Spec (.of Ω)) c).asHom ≫
          condensedSectionOfAdicSection x H v := by
  rw [← adicSheafEquivCondensedModTensorUnitIso_inv_comp_map_smul_comp_hom,
    condensedSectionOfAdicSection, condensedSectionOfAdicSection, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

lemma condensedSectionOfAdicSection_comp_map {S T : Scheme.{u}} (x : S ⟶ T) {H H' : AdicSheaf l T}
    (g : H ⟶ H') (v : AdicSheaf.unit l S ⟶ (x)^*ᵃ[l].obj H) :
    condensedSectionOfAdicSection x H v ≫
        (x)^*⟦Profinite.padicAlgClRingObj l⟧.map ((adicSheafEquivCondensedMod l T).functor.map
            g) =
      condensedSectionOfAdicSection x H' (v ≫ (x)^*ᵃ[l].map g) := by
  have n := (adicUpperStarCompCondensedModIso l x).hom.naturality g
  rw [Functor.comp_map, Functor.comp_map] at n
  rw [condensedSectionOfAdicSection, condensedSectionOfAdicSection, Category.assoc,
    Category.assoc, ← n, Functor.map_comp, Category.assoc]

lemma globalSectionOfModHom_add {Z : Scheme.{u}} {M : AdicSheaf l Z}
    (v v' : AdicSheaf.unit l Z ⟶ M) :
    globalSectionOfModHom (v + v') = globalSectionOfModHom v + globalSectionOfModHom v' := by
  rw [globalSectionOfModHom_eq, globalSectionOfModHom_eq, globalSectionOfModHom_eq]
  erw [Mod.add_hom, Functor.map_add]
  rfl

/-- The global section `v(1)` of `v : ℚ̄_ℓ ⟶ M`,
as an element of the `ℚ̄_ℓ`-vector space of global
sections. -/
noncomputable def adicGlobalSectionOfHom {Z : Scheme.{u}} {M : AdicSheaf l Z}
    (v : AdicSheaf.unit l Z ⟶ M) : (adicGlobalSectionsModule l Z).obj M :=
  globalSectionOfModHom v

lemma adicGlobalSectionOfHom_comp_smul {Z : Scheme.{u}} {M : AdicSheaf l Z}
    (v : AdicSheaf.unit l Z ⟶ M) (c : PadicAlgCl l) :
    adicGlobalSectionOfHom (v ≫
    AdicSheaf.smul (ULift.up c) M) = c • adicGlobalSectionOfHom v := by
  rw [adicGlobalSectionOfHom, globalSectionOfModHom_comp]
  exact LinearMap.congr_fun (adicGlobalSections_map_smul Z c M) _

/-- The Galois action `x^* M ⟶ σ^* x^* M ≅ (σ ≫ x)^* M = x^* M` at a separably closed point,
followed by an endomorphism `f` of `M`. -/
noncomputable def galoisUpperStarEnd {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X) (h : σ ≫ x = x)
    (τ : (σ)^*⟦Profinite.padicAlgClRingObj l⟧ ≅ 𝟭 _)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) (f : M ⟶ M) :
    (x)^*⟦Profinite.padicAlgClRingObj l⟧.obj M ⟶ (x)^*⟦Profinite.padicAlgClRingObj
        l⟧.obj M :=
  τ.inv.app
      ((x)^*⟦Profinite.padicAlgClRingObj l⟧.obj M) ≫
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) σ x).inv.app M ≫
    (CondensedRing.upperStarEqToIso (Profinite.padicAlgClRingObj l) h).hom.app M ≫
    (x)^*⟦Profinite.padicAlgClRingObj l⟧.map f

/-- **The local trace of a scaled Galois action in the two models.** -/
theorem endTensorUnitRingEquiv_traceOrZero_galoisUpperStarEnd {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω)
        ⟶ X)
    (h : σ ≫ x = x) (τ : (σ)^*⟦Profinite.padicAlgClRingObj l⟧ ≅ 𝟭 _)
    (hτ : τ.inv.app 𝟙ₘ = (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj
        l⟧).hom)
    (H : AdicSheaf l X) {r : ℕ}
    (eH : (x)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω)))
    (c : PadicAlgCl l) :
    CondensedRing.endTensorUnitRingEquiv l Ω (traceOrZero (galoisUpperStarEnd σ x h τ
        ((adicSheafEquivCondensedMod l X).functor.obj H)
        ((adicSheafEquivCondensedMod l X).functor.map (AdicSheaf.smul (ULift.up c) H)))) =
      c * LinearMap.trace (PadicAlgCl l) _
        ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections σ x h H)).hom := by
  classical
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have : ConnectedSpace (Spec (.of Ω)) := inferInstanceAs (ConnectedSpace (PrimeSpectrum Ω))
  let b := (adicSheafEquivCondensedModUnitBasis l (Spec (.of Ω)) r).ofIsoBasis
    (((adicUpperStarCompCondensedModIso l x).app H).symm ≪≫
      (adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.mapIso eH)
  have : FiniteDimensional (PadicAlgCl l)
      ((adicGlobalSectionsModule l (Spec (.of Ω))).obj ((x)^*ᵃ[l].obj H)) := by
    have h1 : Module.finrank (PadicAlgCl l)
        ((adicGlobalSectionsModule l (Spec (.of Ω))).obj (AdicSheaf.unit l (Spec (.of Ω)))) = 1 :=
      finrank_globalSections_adicConstantSheaf _
    have : FiniteDimensional (PadicAlgCl l)
        ((adicGlobalSectionsModule l (Spec (.of Ω))).obj (AdicSheaf.unit l (Spec (.of Ω)))) :=
      Module.finite_of_finrank_eq_succ h1
    have : ∀ j : Fin r, Module.Finite (PadicAlgCl l)
        (((adicGlobalSectionsModule l (Spec (.of Ω))).obj ∘
          fun _ ↦ AdicSheaf.unit l (Spec (.of Ω))) j) := fun _ ↦ inferInstanceAs
              (Module.Finite _
          ((adicGlobalSectionsModule l (Spec (.of Ω))).obj (AdicSheaf.unit l (Spec (.of Ω)))))
    exact Module.Finite.equiv (((adicGlobalSectionsModule l (Spec (.of Ω))).mapIso eH ≪≫
      (adicGlobalSectionsModule l (Spec (.of Ω))).mapBiproduct _ ≪≫
      ModuleCat.biproductIsoPi _).toLinearEquiv.symm)
  let A1 : (AdicSheaf.unit l (Spec (.of Ω)) ⟶ (x)^*ᵃ[l].obj H) ≃+
      (adicGlobalSectionsModule l (Spec (.of Ω))).obj ((x)^*ᵃ[l].obj H) :=
    AddEquiv.ofBijective (AddMonoidHom.mk' adicGlobalSectionOfHom globalSectionOfModHom_add)
      (bijective_globalSectionOfModHom _)
  let A2 : (AdicSheaf.unit l (Spec (.of Ω)) ⟶ (x)^*ᵃ[l].obj H) ≃+
      ((adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.obj (AdicSheaf.unit l _) ⟶
        (adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.obj ((x)^*ᵃ[l].obj H)) :=
    AddEquiv.mk' (adicSheafEquivCondensedMod l _).fullyFaithfulFunctor.homEquiv
      (fun _ _ ↦ (adicSheafEquivCondensedMod l _).functor.map_add)
  let A3 : ((adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.obj (AdicSheaf.unit l _) ⟶
        (adicSheafEquivCondensedMod l (Spec (.of Ω))).functor.obj ((x)^*ᵃ[l].obj H)) ≃+
      (𝟙ₘ ⟶ (x)^*⟦Profinite.padicAlgClRingObj l⟧.obj
        ((adicSheafEquivCondensedMod l X).functor.obj H)) :=
    AddEquiv.mk' ((adicSheafEquivCondensedModTensorUnitIso l _).homCongr
      ((adicUpperStarCompCondensedModIso l x).app H))
      (fun _ _ ↦ by simp only [Iso.homCongr_apply, Preadditive.add_comp, Preadditive.comp_add])
  let e := A1.symm.trans (A2.trans A3)
  have he_apply (v : AdicSheaf.unit l (Spec (.of Ω)) ⟶ (x)^*ᵃ[l].obj H) :
      e (adicGlobalSectionOfHom v) = condensedSectionOfAdicSection x H v := by
    have : A1.symm (adicGlobalSectionOfHom v) = v := A1.symm_apply_apply v
    simp only [e, AddEquiv.trans_apply, this]
    rfl
  have hsurj (w : (adicGlobalSectionsModule l (Spec (.of Ω))).obj ((x)^*ᵃ[l].obj H)) :
      ∃ v, adicGlobalSectionOfHom v = w := (bijective_globalSectionOfModHom _).2 w
  have he (c' : PadicAlgCl l) (w) :
      e (c' • w) = (CondensedRing.scalarEndRingHom l (Spec (.of Ω)) c').asHom ≫ e w := by
    obtain ⟨v, rfl⟩ := hsurj w
    rw [← adicGlobalSectionOfHom_comp_smul, he_apply, he_apply, ← AdicSheaf.smul_comp,
      condensedSectionOfAdicSection_smul_comp]
  have hgal (v : AdicSheaf.unit l (Spec (.of Ω)) ⟶ (x)^*ᵃ[l].obj H) :
      ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections σ x h H)).hom
        (adicGlobalSectionOfHom v) = adicGlobalSectionOfHom (adicUpperStarSectionMap σ x h H v) :=
    galoisGlobalSections_globalSectionOfModHom σ x h H v
  refine (CondensedRing.endTensorUnitRingEquiv_traceOrZero_eq_trace b _ e he
    (c • ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections σ x h H)).hom) ?_).trans ?_
  swap
  · rw [map_smul, smul_eq_mul]
    rfl
  intro w
  obtain ⟨v, rfl⟩ := hsurj w
  erw [LinearMap.smul_apply, hgal]
  rw [← adicGlobalSectionOfHom_comp_smul]
  erw [he_apply, he_apply]
  rw [
    ← AdicSheaf.smul_comp, condensedSectionOfAdicSection_smul_comp, galoisUpperStarEnd,
    reassoc_of% (CondensedRing.comp_inv_app_comp_upperStarComp_inv_app_eq_upperStarSectionMap l σ x
      h τ hτ _
      (condensedSectionOfAdicSection x H v)),
    ← condensedSectionOfAdicSection_adicUpperStarSectionMap,
        condensedSectionOfAdicSection_comp_map,
    adicUpperStar_map_smul, ← AdicSheaf.smul_comp, condensedSectionOfAdicSection_smul_comp]

end AlgebraicGeometry.ProEtale
