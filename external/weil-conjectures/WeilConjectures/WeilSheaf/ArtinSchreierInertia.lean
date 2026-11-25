/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FactorGerm
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.StalkFunctor

/-!
# Inertia at infinity acts on the Artin–Schreier sheaf through a character of order `p`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

local notation "Ā" => Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

section Translation

variable (l) in
/-- The translations of `ĀS_* ℚ̄_ℓ` compose: `σ_c ≫ σ_d = σ_{d + c}`. On sections they are the
pullbacks of functions along `(u, x) ↦ (u, σ̄_c x)`. -/
lemma artinSchreierTranslationSheafHom_hom_comp (c d : k₀) :
    (artinSchreierTranslationSheafHom l c).hom ≫ (artinSchreierTranslationSheafHom l d).hom =
      (artinSchreierTranslationSheafHom l (d + c)).hom := by
  ext U : 3
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    artinSchreierTranslationSheafHom_hom_app, artinSchreierTranslationSheafHom_hom_app,
    artinSchreierTranslationSheafHom_hom_app, ← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · simp
  · simp [affineLine.geometricTranslationIso_hom_comp]

variable (l) in
/-- The evaluation `ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along the section `x ↦ (x, σ̄_c x)`, on underlying
sheaves: the pullback of `σ_c` followed by the counit of `ĀS^* ⊣ ĀS_*`. -/
lemma affineLine.artinSchreierEvalHom_hom_eq_counit (c : k₀) :
    (affineLine.artinSchreierEvalHom l c).hom =
      (ĀS)^*[WeilCoefficients.{u} l].map (artinSchreierTranslationSheafHom l c).hom ≫
        (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).counit.app
          (ProEtale.adicConstantSheaf l Ā) := by
  rw [affineLine.artinSchreierEvalHom, Mod.comp_hom', ProEtale.adicUpperStar_map_hom]
  erw [Adjunction.modAdjunction_counit_app_hom]
  rfl

variable (l) in
/-- The translation `σ_c` of `ĀS_* ℚ̄_ℓ` is the pushforward of `ℚ̄_ℓ ≅ σ̄_{c*} ℚ̄_ℓ` followed by
`ĀS_* σ̄_{c*} ≅ ĀS_*`. -/
lemma artinSchreierTranslationSheafHom_hom_eq (c : k₀) :
    (artinSchreierTranslationSheafHom l c).hom =
      (ĀS)_*[WeilCoefficients.{u} l].map
          (ProEtale.adicConstantSheafToLowerStar l (affineLine.geometricTranslationIso k₀ c).hom) ≫
        (ProEtale.lowerStarFactor (WeilCoefficients.{u} l)
          (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
          (ProEtale.adicConstantSheaf l Ā) := by
  rw [artinSchreierTranslationSheafHom_hom, ← ProEtale.lowerStarComp_trans_lowerStarCongr]
  rfl

variable (l) in
/-- **Translating the evaluations.** For the deck transformation `g = σ̄_c` of `ĀS`, with
`g ≫ ĀS = ĀS`, the evaluation along `x ↦ (x, σ̄_{c + d} x)` is the pullback along `g` of the
evaluation along `x ↦ (x, σ̄_d x)`:
```
  ĀS^* ĀS_* ℚ̄_ℓ ───ev_{c + d}────────────────────────────▶ ℚ̄_ℓ
        │                                                   ▲
        │ ≅                                                 │ ≅
        ▼                                                   │
  g^* ĀS^* ĀS_* ℚ̄_ℓ ───g^* ev_d───▶ g^* ℚ̄_ℓ ─────────────────┘
```
-/
lemma affineLine.artinSchreierEvalHom_hom_add (c d : k₀) :
    (affineLine.artinSchreierEvalHom l (c + d)).hom =
      (ProEtale.upperStarFactor (WeilCoefficients.{u} l)
          (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
          ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l Ā)) ≫
        ((affineLine.geometricTranslationIso k₀ c).hom)^*[WeilCoefficients.{u} l].map
          (affineLine.artinSchreierEvalHom l d).hom ≫
        ProEtale.upperStarAdicConstantSheafHom l (affineLine.geometricTranslationIso k₀ c).hom := by
  have hc := ProEtale.upperStar_map_lowerStarFactor_comp_counit (WeilCoefficients.{u} l)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)
    (ProEtale.adicConstantSheafToLowerStar l (affineLine.geometricTranslationIso k₀ c).hom)
  rw [← artinSchreierTranslationSheafHom_hom_eq] at hc
  have n := (ProEtale.upperStarFactor (WeilCoefficients.{u} l)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.naturality
      (X := (ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l Ā))
      (Y := (ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l Ā))
      (artinSchreierTranslationSheafHom l d).hom
  simp only [Functor.comp_map] at n
  rw [affineLine.artinSchreierEvalHom_hom_eq_counit,
    ← artinSchreierTranslationSheafHom_hom_comp,
    Functor.map_comp, Category.assoc, hc]
  rw [reassoc_of% n, affineLine.artinSchreierEvalHom_hom_eq_counit, Functor.map_comp,
    Category.assoc]
  rfl

end Translation
section GlobalSections

variable (k₀ l) in
/-- The underlying sheaf `ĀS_* ℚ̄_ℓ` of the pushforward of the constant sheaf along the
geometric Artin–Schreier map. -/
noncomputable abbrev affineLine.artinSchreierSheaf :
    Sheaf (Scheme.ProEt.topology Ā) (WeilCoefficients.{u} l) :=
  (ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l Ā)

variable (l) in
/-- The evaluation `ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along `x ↦ (x, σ̄_c x)`, as a morphism of the
underlying sheaves. -/
noncomputable def affineLine.artinSchreierEval (c : k₀) :
    (ĀS)^*[WeilCoefficients.{u} l].obj (affineLine.artinSchreierSheaf k₀ l) ⟶
      ProEtale.adicConstantSheaf l Ā :=
  (affineLine.artinSchreierEvalHom l c).hom

lemma affineLine.artinSchreierEval_eq (c : k₀) :
    affineLine.artinSchreierEval l c = (affineLine.artinSchreierEvalHom l c).hom :=
  rfl

/-- The evaluations translate under the deck transformations, on underlying sheaves
(`AlgebraicGeometry.affineLine.artinSchreierEvalHom_hom_add`). -/
lemma affineLine.upperStarFactor_inv_app_comp_artinSchreierEval (c d : k₀) :
    (ProEtale.upperStarFactor (WeilCoefficients.{u} l)
        (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).inv.app
        (affineLine.artinSchreierSheaf k₀ l) ≫ affineLine.artinSchreierEval l (c + d) =
      ((affineLine.geometricTranslationIso k₀ c).hom)^*[WeilCoefficients.{u} l].map
          (affineLine.artinSchreierEval l d) ≫
        ProEtale.upperStarAdicConstantSheafHom l (affineLine.geometricTranslationIso k₀ c).hom := by
  rw [affineLine.artinSchreierEval_eq, affineLine.artinSchreierEvalHom_hom_add,
    Iso.inv_hom_id_app_assoc]
  rfl

/-- The global sections of `ĀS^* ĀS_* ℚ̄_ℓ` are determined by their evaluations along the
sections `x ↦ (x, σ̄_c x)`, `c ∈ k₀`. -/
lemma affineLine.eq_of_globalSections_artinSchreierEval
    {z z' : (Sheaf.Γ (Scheme.ProEt.topology Ā) (WeilCoefficients.{u} l)).obj
      ((ĀS)^*[WeilCoefficients.{u} l].obj (affineLine.artinSchreierSheaf k₀ l))}
    (h : ∀ c, ((Sheaf.Γ _ _).map (affineLine.artinSchreierEval l c)).hom z =
      ((Sheaf.Γ _ _).map (affineLine.artinSchreierEval l c)).hom z') : z = z' := by
  let adj := constantSheafΓAdj (Scheme.ProEt.topology Ā) (WeilCoefficients.{u} l)
  let R := ModuleCat.of (ULift.{u + 1} (PadicAlgCl l)) (ULift.{u + 1} (PadicAlgCl l))
  let f (x : (Sheaf.Γ (Scheme.ProEt.topology Ā) (WeilCoefficients.{u} l)).obj
      ((ĀS)^*[WeilCoefficients.{u} l].obj (affineLine.artinSchreierSheaf k₀ l))) :
      R ⟶ (Sheaf.Γ _ _).obj
        ((ĀS)^*[WeilCoefficients.{u} l].obj (affineLine.artinSchreierSheaf k₀ l)) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  have hf : f z = f z' := by
    have : (adj.homEquiv _ _).symm (f z) = (adj.homEquiv _ _).symm (f z') := by
      refine affineLine.artinSchreierEvalHom_hom_ext fun c ↦ ?_
      change (adj.homEquiv _ _).symm (f z) ≫ affineLine.artinSchreierEval l c =
        (adj.homEquiv _ _).symm (f z') ≫ affineLine.artinSchreierEval l c
      rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_right_symm]
      congr 1
      ext
      simp only [f, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, one_smul]
      exact h c
    simpa using this
  have := congrArg (fun φ : R ⟶ _ ↦ φ.hom (1 : ULift.{u + 1} (PadicAlgCl l))) hf
  simp only [f, ModuleCat.hom_ofHom] at this
  rwa [LinearMap.toSpanSingleton_apply_one, LinearMap.toSpanSingleton_apply_one] at this

variable (l) in
/-- The global section `x ↦ ((x, σ̄_c x) ↦ ψ(c))` of `ĀS^* ĀS_* ℚ̄_ℓ`, the image of `1` under the
splitting map: it spans the `ψ`-isotypic line. -/
noncomputable def affineLine.artinSchreierSplitSection (ψ : AddChar k₀ (PadicAlgCl l)) :
    (Sheaf.Γ (Scheme.ProEt.topology Ā) (WeilCoefficients.{u} l)).obj
      ((ĀS)^*[WeilCoefficients.{u} l].obj (affineLine.artinSchreierSheaf k₀ l)) :=
  ProEtale.globalSectionOfModHom (affineLine.artinSchreierSplitModHom l ψ)

/-- The evaluation of the split section along `x ↦ (x, σ̄_c x)` is the constant `ψ(c)`. -/
lemma affineLine.Γ_map_artinSchreierEval_splitSection (ψ : AddChar k₀ (PadicAlgCl l))
    (c : k₀) :
    ((Sheaf.Γ _ _).map (affineLine.artinSchreierEval l c)).hom
        (affineLine.artinSchreierSplitSection l ψ) =
      ULift.up (ψ c) • ProEtale.oneGlobalSection (l := l) Ā := by
  have hm : (affineLine.artinSchreierSplitModHom l ψ).hom ≫ affineLine.artinSchreierEval l c =
      ULift.up (ψ c) • 𝟙 (ProEtale.adicConstantSheaf l Ā) := by
    rw [affineLine.artinSchreierSplitModHom_hom, Category.assoc]
    exact affineLine.artinSchreierSplitHom_comp_evalHom ψ c
  have h := congrArg (fun φ ↦ ((Sheaf.Γ (Scheme.ProEt.topology Ā) (WeilCoefficients.{u} l)).map
    φ).hom (ProEtale.oneGlobalSection (l := l) Ā)) hm
  simp only [Functor.map_comp, Functor.map_smul, CategoryTheory.Functor.map_id,
    ConcreteCategory.comp_apply] at h
  rw [affineLine.artinSchreierSplitSection, ProEtale.globalSectionOfModHom_eq]
  exact h

/-- **The deck transformations act on the split section through `ψ`.** The germ along the deck
transformation `σ̄_c` of `ĀS`, which is the pullback of global sections of `ĀS^* ĀS_* ℚ̄_ℓ`
along `σ̄_c`, multiplies the split section by `ψ(-c)`. -/
lemma affineLine.germ_artinSchreierSplitSection (ψ : AddChar k₀ (PadicAlgCl l)) (c : k₀) :
    (ProEtale.factorGerm (WeilCoefficients.{u} l)
        (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)
        (affineLine.artinSchreierSheaf k₀ l)).hom (affineLine.artinSchreierSplitSection l ψ) =
      ULift.up (ψ (-c)) • affineLine.artinSchreierSplitSection l ψ := by
  set g := (affineLine.geometricTranslationIso k₀ c).hom
  have hg := affineLine.geometricTranslation_comp_artinSchreierMap k₀ c
  have key (d : k₀) : ProEtale.factorGerm (WeilCoefficients.{u} l) hg
      (affineLine.artinSchreierSheaf k₀ l) ≫
        (Sheaf.Γ _ _).map (affineLine.artinSchreierEval l (c + d)) =
      (Sheaf.Γ _ _).map (affineLine.artinSchreierEval l d) ≫
        (ProEtale.globalSectionsToUpperStar _ g).app (ProEtale.adicConstantSheaf l Ā) ≫
        (Sheaf.Γ _ _).map (ProEtale.upperStarAdicConstantSheafHom l g) := by
    have n := (ProEtale.globalSectionsToUpperStar (WeilCoefficients.{u} l) g).naturality
      (affineLine.artinSchreierEval l d)
    simp only [Functor.comp_map] at n
    rw [ProEtale.factorGerm, Category.assoc, ← Functor.map_comp,
      affineLine.upperStarFactor_inv_app_comp_artinSchreierEval, Functor.map_comp,
      reassoc_of% n]
  refine affineLine.eq_of_globalSections_artinSchreierEval fun d' ↦ ?_
  obtain ⟨d, rfl⟩ : ∃ d, d' = c + d := ⟨d' - c, by ring⟩
  have h₁ := congrArg (fun φ ↦ φ.hom (affineLine.artinSchreierSplitSection l ψ)) (key d)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  rw [h₁, affineLine.Γ_map_artinSchreierEval_splitSection, map_smul, map_smul,
    map_smul, affineLine.Γ_map_artinSchreierEval_splitSection, ProEtale.oneGlobalSection_eq]
  erw [ProEtale.globalSectionsToUpperStar_adicConstantGlobalSection]
  rw [smul_smul]
  congr 1
  exact congrArg ULift.up (by rw [← AddChar.map_add_eq_mul, neg_add_cancel_left])

end GlobalSections
section ConstantStalk

/-- Every section of the pullback `y^* ℚ̄_ℓ,V` of the constant sheaf to the spectrum of a field is
a multiple of the restriction of the unit section `1`. -/
lemma ProEtale.exists_eq_smul_globalSectionsToUpperStar_oneGlobalSection {Ω : Type u} [Field Ω]
    {V : Scheme.{u}} (y : Spec (.of Ω) ⟶ V)
    (v : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of Ω))) (WeilCoefficients.{u} l)).obj
      ((y)^*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l V))) :
    ∃ c : ULift.{u + 1} (PadicAlgCl l), v = c • ((ProEtale.globalSectionsToUpperStar _ y).app
      (ProEtale.adicConstantSheaf l V)).hom (ProEtale.oneGlobalSection V) := by
  let φ := (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of Ω))) (WeilCoefficients.{u} l)).map
    (ProEtale.upperStarAdicConstantSheafHom l y)
  have hφ : Function.Injective φ.hom :=
    (ConcreteCategory.bijective_of_isIso φ).1
  let e := (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology (Spec (.of Ω)))
    (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId _)).app
      (ProEtale.adicConstantSheaf l (Spec (.of Ω)))
  let f : PadicAlgCl.locallyFiniteFunctions l (Spec (.of Ω)) := (e.hom.hom (φ.hom v)).down
  have hv : φ.hom v = ProEtale.adicConstantGlobalSection f := by
    change _ = e.inv.hom (ULift.up f)
    exact (congrArg (fun ψ ↦ ψ.hom (φ.hom v)) e.hom_inv_id).symm
  have : PreconnectedSpace (Spec (.of Ω)) := inferInstance
  have hf := PadicAlgCl.locallyFiniteFunctions_eq_algebraMap f (IsLocalRing.closedPoint Ω)
  obtain ⟨a, ha⟩ : ∃ a, f = algebraMap (PadicAlgCl l) _ a := ⟨_, hf⟩
  have h1 : PadicAlgCl.locallyFiniteFunctionsComp l y.base.hom 1 = 1 := rfl
  refine ⟨ULift.up a, hφ ?_⟩
  rw [map_smul, ProEtale.oneGlobalSection_eq,
    ProEtale.globalSectionsToUpperStar_adicConstantGlobalSection, hv, ha,
    Algebra.algebraMap_eq_smul_one, h1]
  unfold ProEtale.adicConstantGlobalSection
  rw [← map_smul]
  rfl

end ConstantStalk

end AlgebraicGeometry
