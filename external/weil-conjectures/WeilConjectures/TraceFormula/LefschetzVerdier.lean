/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PointNormalization
public import WeilConjectures.TraceFormula.ProperCompatibility
public import WeilConjectures.TraceFormula.TraceClassAdditivity

/-!

# The Lefschetz–Verdier formula

For `X` proper over `s = Spec k` and an endocorrespondence `c = (C, c₁, c₂, u)` of `(X, K)` with
proper ordinary leg, the trace of the global operator is the integral of the trace class
(blueprint `theorem-proper-pushforward-lefschetz-verdier--2`):
```
tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u).
```
Following the blueprint proof, `(a_X, a_C) : (C, c) ⟶ (s, (𝟙, 𝟙))` is a proper pushforward
diagram (`ProEtale.CondensedRing.Correspondence.toPointDiagram`) and

1. the pushed coefficient map `[a_X, a_C]_! u` is the global operator `T_c(u)`, read through
   `Ra_{X!} ≅ Ra_{X*}` (`Correspondence.globalOperator_eq_pushforwardCoeff`): its ordinary half
   is the unit of `Lc₂^* ⊣ Rc₂_*` by the triangle identities, and its exceptional half is the
   composition isomorphism followed by the counit of `Rc₁_! ⊣ Rc₁^!`;
2. the proper pushforward compatibility of the trace class
   (`Correspondence.ProperPushforwardDiagram.traceClassPushforward_eq`) identifies
   `(a_Fix)_* Tr_c(u) = ∫_Fix(c) Tr_c(u)` with the trace class of the pushed correspondence;
3. the point normalization (`Correspondence.integral_traceClass_ofEnd`) gives the trace.

## Main statements

- `ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_integral_traceClass`: the
  Lefschetz–Verdier formula.
- `ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_sum_localTerm`: the
  Lefschetz–Verdier trace comparison with the sum of the local terms.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {P X C : Type*} [Category* P] [Category* X] [Category* C]

/-- The unit of a composite adjunction through the conjugate of a composition isomorphism
`σ : L_g ≅ L_f ⋙ L_c`: with `λ : R_c ⋙ R_f ≅ R_g` the conjugate of `σ`,
`R_f η_c ≫ λ = η_g ≫ R_g (σ ≫ L_c ε_f)`. -/
lemma map_unit_comp_conjugateIsoEquiv_inv_app {Lf : P ⥤ X} {Rf : X ⥤ P} {Lc : X ⥤ C}
    {Rc : C ⥤ X} {Lg : P ⥤ C} {Rg : C ⥤ P} (adjf : Lf ⊣ Rf) (adjc : Lc ⊣ Rc) (adjg : Lg ⊣ Rg)
    (σ : Lg ≅ Lf ⋙ Lc) (K : X) :
    Rf.map (adjc.unit.app K) ≫
        (conjugateIsoEquiv adjg (adjf.comp adjc) σ.symm).inv.app (Lc.obj K) =
      adjg.unit.app (Rf.obj K) ≫ Rg.map (σ.hom.app (Rf.obj K) ≫ Lc.map (adjf.counit.app K)) := by
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv, conjugateEquiv_apply_app,
    Adjunction.comp_counit_app, Functor.comp_obj]
  have h1 := adjg.unit.naturality (Rf.map (adjc.unit.app K))
  have h2 := σ.hom.naturality (Rf.map (adjc.unit.app K))
  have h3 := adjf.counit.naturality (adjc.unit.app K)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h1 h2 h3
  rw [reassoc_of% h1, ← Rg.map_comp, ← Rg.map_comp]
  congr 2
  rw [reassoc_of% h2, ← Lc.map_comp_assoc, h3, Lc.map_comp, Category.assoc,
    Adjunction.left_triangle_components, Category.comp_id]

/-- For an adjunction `L ⊣ R` with `Λ : L ≅ 𝟭`, the unit followed by the conjugate
`R ≅ 𝟭` of `Λ` is `Λ⁻¹`. -/
@[reassoc]
lemma unit_map_comp_conjugateIsoEquiv_hom_app {L R : P ⥤ P} (adj : L ⊣ R) (Λ : L ≅ 𝟭 P)
    {Z Y : P} (φ : L.obj Z ⟶ Y) :
    adj.unit.app Z ≫ R.map φ ≫ (conjugateIsoEquiv adj Adjunction.id Λ.symm).hom.app Y =
      Λ.inv.app Z ≫ φ := by
  simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom, conjugateEquiv_apply_app]
  have h1 := Λ.inv.naturality (R.map φ)
  have h2 := Λ.inv.naturality (adj.unit.app Z)
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at h1 h2
  simp only [Adjunction.id, Functor.id_map, Functor.id_obj, Category.id_comp, NatTrans.id_app]
  rw [reassoc_of% h1, reassoc_of% h2, Adjunction.counit_naturality,
    Adjunction.left_triangle_components_assoc]

/-- Abstract form of the ordinary half of the global operator: the unit of `L_c ⊣ R_c` read
through the lower shriek functors `S_f, S_c, S_g` (`ι : S ≅ R`) and the composition isomorphism
`κ : S_g ≅ S_c ⋙ S_f` is the unit of `L_g ⊣ R_g` followed by the counit of `L_f ⊣ R_f`, up to
`Θ : L_1 ≅ 𝟭`. -/
lemma map_unit_comp_inv_eq_aux {Lf : P ⥤ X} {Rf Sf : X ⥤ P} {Lc : X ⥤ C} {Rc Sc : C ⥤ X}
    {Lg : P ⥤ C} {Rg Sg : C ⥤ P} {L1 : P ⥤ P} (adjf : Lf ⊣ Rf) (adjc : Lc ⊣ Rc)
    (adjg : Lg ⊣ Rg) (σ : Lg ≅ Lf ⋙ Lc) (ιf : Sf ≅ Rf) (ιc : Sc ≅ Rc) (ιg : Sg ≅ Rg)
    (κ : Sg ≅ Sc ⋙ Sf) (lam : Rc ⋙ Rf ≅ Rg)
    (hκ : ∀ M, κ.hom.app M ≫ ιf.hom.app (Sc.obj M) ≫ Rf.map (ιc.hom.app M) =
      ιg.hom.app M ≫ lam.inv.app M)
    (hlam : ∀ K, Rf.map (adjc.unit.app K) ≫ lam.hom.app (Lc.obj K) =
      adjg.unit.app (Rf.obj K) ≫ Rg.map (σ.hom.app (Rf.obj K) ≫ Lc.map (adjf.counit.app K)))
    (Θ : L1 ≅ 𝟭 P) (K : X) :
    Sf.map (adjc.unit.app K) ≫ Sf.map (ιc.inv.app (Lc.obj K)) ≫ κ.inv.app (Lc.obj K) =
      ιf.hom.app K ≫ Θ.inv.app (Rf.obj K) ≫ adjg.unit.app (L1.obj (Rf.obj K)) ≫
        Rg.map (Lg.map (Θ.hom.app (Rf.obj K)) ≫ σ.hom.app (Rf.obj K) ≫
          Lc.map (adjf.counit.app K)) ≫ ιg.inv.app (Lc.obj K) := by
  have e (M : C) : κ.inv.app M =
      ιf.hom.app (Sc.obj M) ≫ Rf.map (ιc.hom.app M) ≫ lam.hom.app M ≫ ιg.inv.app M := by
    rw [← cancel_epi (κ.hom.app M), Iso.hom_inv_id_app, reassoc_of% (hκ M)]
    simp
  have hu := adjg.unit.naturality (Θ.hom.app (Rf.obj K))
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hu
  rw [e, ← Sf.map_comp_assoc, ιf.hom.naturality_assoc, ← Rf.map_comp_assoc, Category.assoc]
  simp only [Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj, Functor.id_obj]
  rw [reassoc_of% (hlam K)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hu, Iso.inv_hom_id_app_assoc]

/-- A component of the mate of a two-square. -/
lemma mateEquiv_app_eq {D E : Type*} [Category* D] [Category* E] {G : C ⥤ D} {H : X ⥤ E}
    {L₁ : C ⥤ X} {R₁ : X ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (d : X) :
    (mateEquiv adj₁ adj₂ α).app d = adj₂.unit.app (G.obj (R₁.obj d)) ≫
      R₂.map (α.app (R₁.obj d) ≫ H.map (adj₁.counit.app d)) := by
  simp [mateEquiv_apply]

/-- Abstract form of the exceptional half of the global operator: the mate of the composition
isomorphism `Ξ = S_1 ι_g⁻¹ ≫ κ₁⁻¹ ≫ e ≫ κ₂ ≫ ι_f`, read through `R_1 ≅ 𝟭` and the
identifications `ι`, is the composition isomorphism followed by the counit. -/
lemma mateEquiv_app_comp_eq_aux {Sg Rg Sg' Sg'' : C ⥤ P} {S1 U1 : P ⥤ P} {Sc1 : C ⥤ X}
    {Uc1 : X ⥤ C} {Sf Rf : X ⥤ P} (adj1 : S1 ⊣ U1) (adjc1 : Sc1 ⊣ Uc1) (Λ : S1 ≅ 𝟭 P)
    (ιg : Sg ≅ Rg) (ιf : Sf ≅ Rf) (κ1 : Sg' ≅ Sg ⋙ S1) (θ1 : Sg ⟶ Sg')
    (hκ1 : ∀ M, κ1.inv.app M = Λ.hom.app (Sg.obj M) ≫ θ1.app M)
    (eqIso : Sg' ≅ Sg'') (κ2 : Sg'' ≅ Sc1 ⋙ Sf) (K : X) :
    ιg.hom.app (Uc1.obj K) ≫
        (mateEquiv adjc1 adj1 (Functor.isoWhiskerRight ιg.symm S1 ≪≫ κ1.symm ≪≫ eqIso ≪≫ κ2 ≪≫
          Functor.isoWhiskerLeft Sc1 ιf).hom).app K ≫
        (conjugateIsoEquiv adj1 Adjunction.id Λ.symm).hom.app (Rf.obj K) ≫ ιf.inv.app K =
      θ1.app (Uc1.obj K) ≫ eqIso.hom.app _ ≫ κ2.hom.app _ ≫ Sf.map (adjc1.counit.app K) := by
  rw [mateEquiv_app_eq]
  simp only [Category.assoc]
  have hn := Λ.inv.naturality (ιg.inv.app (Uc1.obj K))
  simp only [Functor.id_map, Functor.id_obj] at hn
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  erw [unit_map_comp_conjugateIsoEquiv_hom_app_assoc]
  have hf := ιf.inv.naturality (adjc1.counit.app K)
  simp only [Functor.comp_obj, Functor.id_obj] at hf
  simp only [Category.assoc, hκ1]
  rw [← reassoc_of% hn, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc, hf,
    Iso.hom_inv_id_app_assoc]

/-- Assembling a composite from two equations of partial composites. -/
lemma assemble_aux {A B B' B'' D E F : P} {a₁ : A ⟶ B} {a₂ : B ⟶ B'} {a₃ : B' ⟶ B''}
    {p : A ⟶ B''} (hA : a₁ ≫ a₂ ≫ a₃ = p) (u : B'' ⟶ D) {b₁ : D ⟶ E} {b₂ : E ⟶ F}
    {q : D ⟶ F} (hB : q = b₁ ≫ b₂) :
    a₁ ≫ a₂ ≫ a₃ ≫ u ≫ b₁ ≫ b₂ = p ≫ u ≫ q := by
  rw [← hA, hB]
  simp only [Category.assoc]

/-- Assemble two partial composites around a functorial map, transporting that map through
a natural isomorphism. -/
private lemma assemble_natIso_aux {S R : C ⥤ P} (ι : S ≅ R) {A B B' D E F H : P} {M N : C}
    {a₁ : A ⟶ B} {a₂ : B ⟶ B'} {a₃ : B' ⟶ S.obj M}
    {p₁ : A ⟶ D} {p₂ : D ⟶ E} {p₃ : E ⟶ R.obj M}
    (hA : a₁ ≫ a₂ ≫ a₃ = p₁ ≫ p₂ ≫ p₃ ≫ ι.inv.app M) (u : M ⟶ N)
    {b₁ : S.obj N ⟶ F} {b₂ : F ⟶ A}
    {q₁ : R.obj N ⟶ H} {q₂ : H ⟶ D} {q₃ : D ⟶ A}
    (hB : ι.hom.app N ≫ q₁ ≫ q₂ ≫ q₃ = b₁ ≫ b₂) :
    a₁ ≫ a₂ ≫ a₃ ≫ S.map u ≫ b₁ ≫ b₂ =
      p₁ ≫ (p₂ ≫ (p₃ ≫ R.map u ≫ q₁) ≫ q₂) ≫ q₃ := by
  rw [assemble_aux hA (S.map u) hB]
  simp only [Category.assoc]
  rw [← ι.inv.naturality_assoc, Iso.inv_hom_id_app_assoc]
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Coherence

variable {C X Y : Over (Spec (.of k))} [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (ℓ) in
/-- The right unit law for the composition isomorphisms of the derived pullbacks, inverse form. -/
@[reassoc]
lemma boundedConstructibleUpperStarComp_id_right_inv_app (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f (𝟙 Y)).inv.app K ≫
        eqToHom (by rw [Category.comp_id]; rfl) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).hom.app K) := by
  rw [← cancel_epi ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f
    (𝟙 Y)).hom.app K), Iso.hom_inv_id_app_assoc, boundedConstructibleUpperStarComp_id_right_app]

variable (ℓ) in
/-- The right unit law for the composition isomorphisms of the lower shriek, inverse form. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_id_right_inv_app (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y)).inv.app K =
      (boundedConstructibleLowerShriekId ℓ Y).hom.app _ ≫
        eqToHom (by rw [Category.comp_id]; rfl) := by
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (𝟙 Y)).hom.app K),
    Iso.hom_inv_id_app, boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app,
    ← Category.assoc, boundedConstructibleLowerShriekComp_padicAlgCl_id_right ℓ f K,
    eqToHom_trans, eqToHom_refl]

variable (ℓ) in
/-- The ordinary half of the global operator (blueprint
`theorem-proper-pushforward-lefschetz-verdier--2`, proof): for `c₂ ≫ f = g`, the unit of
`Lc₂^* ⊣ Rc₂_*` read on `Rf_!` is the ordinary half `γ` of the coefficient pushforward along
`(f, g)`. -/
lemma lowerShriek_map_unit_eq_pushforwardCoeffUnit_aux (c₂ : C ⟶ X) (f : X ⟶ Y) (g : C ⟶ Y)
    [IsProper c₂.left] [IsProper f.left] [IsProper g.left] (hg : c₂ ≫ f = g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ c₂).unit.app K) ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c₂).inv.app _) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₂ f).inv.app _ ≫
      eqToHom (by rw [hg]; rfl) =
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K ≫
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).inv.app _ ≫
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app _ ≫
        (boundedConstructibleLowerStar ℓ g).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g (𝟙 Y)).inv.app
              _ ≫
            eqToHom (by rw [Category.comp_id, hg]; rfl) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c₂ f).hom.app
              _ ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).map
              ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K))) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app _ := by
  subst hg
  rw [boundedConstructibleUpperStarComp_id_right_inv_app_assoc]
  simp only [eqToHom_refl, Category.comp_id, Category.assoc]
  exact CategoryTheory.map_unit_comp_inv_eq_aux
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ c₂)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (c₂ ≫ f))
    (boundedConstructibleUpperStarComp _ ℓ c₂ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c₂)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (c₂ ≫ f))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₂ f)
    (boundedConstructibleLowerStarComp ℓ c₂ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ c₂ f)
    (CategoryTheory.map_unit_comp_conjugateIsoEquiv_inv_app _ _ _ _)
    (boundedConstructibleUpperStarId _ ℓ Y) K

variable (ℓ) in
/-- The exceptional half of the global operator (blueprint
`theorem-proper-pushforward-lefschetz-verdier--2`, proof): for a square `g ≫ 𝟙 = c₁ ≫ f`, the
exchange map `E : Rg_* Rc₁^! ⟶ R(𝟙)^! Rf_*`, read on `Rg_!` and `Rf_!` through `R(𝟙)^! ≅ 𝟭`, is the
composition isomorphism followed by the counit of `Rc₁_! ⊣ Rc₁^!`. -/
lemma lowerStarUpperShriekExchange_app_id_aux (c₁ : C ⟶ X) (f : X ⟶ Y) (g : C ⟶ Y)
    [IsProper f.left] [IsProper g.left] (w : g ≫ 𝟙 Y = c₁ ≫ f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).hom.app _ ≫
        (lowerStarUpperShriekExchange ℓ w).app K ≫
        (boundedConstructibleUpperShriekId ℓ Y).hom.app _ ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app K =
      eqToHom (by rw [← w, Category.comp_id]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₁ f).hom.app _ ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleUpperShriekAdjunction ℓ
            c₁).counit.app K) := by
  have e1 : boundedConstructibleUpperShriekId ℓ Y = conjugateIsoEquiv
      (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 Y)) Adjunction.id
      (boundedConstructibleLowerShriekId ℓ Y).symm := rfl
  have e2 : lowerStarUpperShriekExchange ℓ w = CategoryTheory.mateEquiv
      (boundedConstructibleUpperShriekAdjunction ℓ c₁)
      (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 Y))
      (lowerStarLowerShriekCompIso ℓ w).hom := rfl
  have e3 : lowerStarLowerShriekCompIso ℓ w =
      Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).symm _ ≪≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (𝟙 Y)).symm ≪≫
      eqToIso (congrArg (boundedConstructibleLowerShriek ℓ) w) ≪≫
      boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₁ f ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f) := rfl
  rw [e1, e2, e3]
  have h := CategoryTheory.mateEquiv_app_comp_eq_aux
    (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 Y))
    (boundedConstructibleUpperShriekAdjunction ℓ c₁)
    (boundedConstructibleLowerShriekId ℓ Y)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (𝟙 _))
    (eqToHom (by rw [Category.comp_id]))
    (fun M ↦ by rw [boundedConstructibleLowerShriekComp_padicAlgCl_id_right_inv_app, eqToHom_app])
    (eqToIso (congrArg (boundedConstructibleLowerShriek ℓ) w))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c₁ f) K
  refine h.trans ?_
  simp only [eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]
end Coherence

namespace Correspondence

variable {X : Over (Spec (.of k))} [QuasiCompact X.hom] [IsProper X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The support of an endocorrespondence of a proper scheme with proper ordinary leg is proper. -/
instance isProper_C_hom [IsProper c.c₂.left] : IsProper c.C.hom := by
  rw [← Over.w c.c₂]
  infer_instance

/-- The proper pushforward diagram `(a_X, a_C) : (C, c) ⟶ (s, (𝟙, 𝟙))` to the point
(blueprint `theorem-proper-pushforward-lefschetz-verdier--2`, proof). -/
noncomputable abbrev toPointDiagram [IsProper c.c₂.left] :
    c.ProperPushforwardDiagram (point k) where
  f := toPoint X
  D := point k
  b₁ := 𝟙 _
  b₂ := 𝟙 _
  g := toPoint c.C
  w₁ := toPoint_ext _ _
  w₂ := toPoint_ext _ _

/-- The exceptional half of the global operator (blueprint
`theorem-proper-pushforward-lefschetz-verdier--2`, proof): the exceptional half `δ` of the
coefficient pushforward along `(a_X, a_C)`, read on `Ra_{C!}` and `Ra_{X!}`, is the composition
isomorphism followed by the counit of `Rc₁_! ⊣ Rc₁^!`. -/
lemma lowerShriekIsoLowerStar_hom_app_comp_pushforwardCoeffCounit [IsProper c.c₂.left] :
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint c.C)).hom.app _ ≫
        c.toPointDiagram.pushforwardCoeffCounit ≫
        (boundedConstructibleUpperShriekId ℓ (point k)).hom.app c.toPointDiagram.coeff ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.app K =
      (boundedConstructibleLowerShriekCompToPoint ℓ c.c₁).inv.app _ ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ
            c.c₁).counit.app K) := by
  rw [boundedConstructibleLowerShriekCompToPoint_inv_app, Category.assoc]
  have e1 : c.toPointDiagram.pushforwardCoeffCounit =
      (lowerStarUpperShriekExchange ℓ c.toPointDiagram.w₁).app K := rfl
  have e2 : lowerStarUpperShriekExchange ℓ c.toPointDiagram.w₁ = lowerStarUpperShriekExchange ℓ
      (toPoint_ext _ _ : toPoint c.C ≫ 𝟙 (point k) = c.c₁ ≫ toPoint X) := rfl
  rw [e1, e2]
  exact lowerStarUpperShriekExchange_app_id_aux ℓ c.c₁ (toPoint X) (toPoint c.C) _ K

/-- The ordinary half of the global operator (blueprint
`theorem-proper-pushforward-lefschetz-verdier--2`, proof): the unit of `Lc₂^* ⊣ Rc₂_*` read on
`Ra_{X!}` and `Ra_{C!}` is the ordinary half `γ` of the coefficient pushforward along
`(a_X, a_C)`. -/
lemma lowerShriek_map_unit_eq_pushforwardCoeffUnit [IsProper c.c₂.left] :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ c.c₂).unit.app K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ c.c₂).inv.app _) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ c.c₂).hom.app _ =
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).hom.app K ≫
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).inv.app
        c.toPointDiagram.coeff ≫
      c.toPointDiagram.pushforwardCoeffUnit ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint c.C)).inv.app _ := by
  rw [boundedConstructibleLowerShriekCompToPoint_hom_app]
  have e : c.toPointDiagram.pushforwardCoeffUnit =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint c.C)).unit.app _ ≫
        (boundedConstructibleLowerStar ℓ (toPoint c.C)).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint c.C)
              (𝟙 (point k))).inv.app _ ≫
            eqToHom (by rw [Category.comp_id, comp_toPoint]) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂
              (toPoint X)).hom.app _ ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
              ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint X)).counit.app K)) :=
    rfl
  rw [e]
  exact lowerShriek_map_unit_eq_pushforwardCoeffUnit_aux ℓ c.c₂ (toPoint X) (toPoint c.C)
    (comp_toPoint _) K

/-- **The pushed coefficient map is the global operator** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--2`, proof): the coefficient pushforward
`[a_X, a_C]_! u` of `u` along the diagram to the point is the global operator `T_c(u)`, read through
`Ra_{X!} ≅ Ra_{X*}` and `L(𝟙)^* ≅ 𝟭 ≅ R(𝟙)^!`. -/
theorem globalOperator_eq_pushforwardCoeff [IsProper c.c₂.left] :
    c.globalOperator =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).hom.app K ≫
        ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).inv.app
          c.toPointDiagram.coeff ≫
          c.toPointDiagram.pushforwardCoeff ≫
          (boundedConstructibleUpperShriekId ℓ (point k)).hom.app c.toPointDiagram.coeff) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).inv.app K := by
  exact c.globalOperator_eq.trans
    (CategoryTheory.assemble_natIso_aux
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint c.C))
      c.lowerShriek_map_unit_eq_pushforwardCoeffUnit c.u
      c.lowerShriekIsoLowerStar_hom_app_comp_pushforwardCoeffCounit)

/-- **The Lefschetz–Verdier formula** (blueprint `theorem-proper-pushforward-lefschetz-verdier--2`,
`theorem-proper-pushforward-lefschetz-verdier--2`): for `X` proper over `s`, an endocorrespondence
`c` with proper ordinary leg `c₂` and proper fixed locus,
the trace of the global operator is the integral of the trace class,
`tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u)`.

The proof pushes `c` forward to the point along `(a_X, a_C)`: the pushed coefficient map is the
global operator (`globalOperator_eq_pushforwardCoeff`), the proper pushforward compatibility
(`ProperPushforwardDiagram.traceClassPushforward_eq`) identifies the pushforward
`(a_Fix)_* Tr_c(u)`, which is the integral, with the trace class of the pushed correspondence,
and the point normalization (`integral_traceClass_ofEnd`) gives its trace. -/
theorem trace_globalOperator_eq_integral_traceClass [IsProper c.c₂.left]
    (F : c.FixedLocus) [IsProper F.F.hom]
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)] :
    End.of (trace c.globalOperator) = (c.traceClass F).integral := by
  obtain ⟨T, hT⟩ : ∃ T : c.toPointDiagram.coeff ⟶ c.toPointDiagram.coeff, T =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).inv.app
        c.toPointDiagram.coeff ≫ c.toPointDiagram.pushforwardCoeff ≫
        (boundedConstructibleUpperShriekId ℓ (point k)).hom.app c.toPointDiagram.coeff :=
    ⟨_, rfl⟩
  let : HasRightDual c.toPointDiagram.coeff :=
    @HasRightDual.mk _ _ _ _ (HasRightDual.rightDual ((boundedConstructibleLowerShriek
      ℓ (toPoint X)).obj K)) (exactPairingCongrLeft
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).app K).symm)
  have h₁ : trace c.globalOperator = trace T :=
    trace_eq_of_iso ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint X)).app K)
      c.globalOperator T (by rw [globalOperator_eq_pushforwardCoeff, hT]; simp)
  let Fb : c.toPointDiagram.pushforward.FixedLocus :=
    (fixedLocusOfEnd T).withCoeff _ c.toPointDiagram.pushforwardCoeff
  have : IsProper Fb.F.hom := inferInstanceAs (IsProper (point k).hom)
  have h₂ := c.toPointDiagram.traceClassPushforward_eq F Fb
  rw [ProperPushforwardDiagram.traceClassPushforward] at h₂
  have hu : c.toPointDiagram.pushforwardCoeff = (ofEnd _ T).u := by
    rw [hT]
    simp [ofEnd]
  have h₃ : c.toPointDiagram.pushforward.traceClass Fb =
      (ofEnd _ T).traceClass (fixedLocusOfEnd T) := by
    refine (rfl : _ = (fixedLocusOfEnd T).traceClassWithCoeff _
      c.toPointDiagram.pushforwardCoeff).trans ?_
    rw [hu]
    rfl
  rw [h₁, ← integral_traceClass_ofEnd T,
    BorelMooreSection.integral_eq_integral_pushforward (c.traceClass F),
    BorelMooreSection.pushforward_congr (toPoint_ext (toPoint F.F) (c.toPointDiagram.fixMap F Fb)),
    h₂, h₃]

/-- **The Lefschetz–Verdier trace comparison** (blueprint
`theorem-proper-pushforward-lefschetz-verdier`): for `X` proper over `s`, an endocorrespondence with
proper ordinary leg and a fixed locus which is the disjoint union of finitely many open and closed
subschemes `j_β : B_β ⟶ Fix(c)` proper over `s`, the trace of the global operator is the sum of the
local terms, `tr(T_c(u) | RΓ_c(X, K)) = ∑_β LT_β(u)`. It is the fixed-point localization
`trace_globalOperator_eq_integral_traceClass` followed by the decomposition of the integral
into local terms (`BorelMooreSection.integral_eq_sum_localTerm`). -/
theorem trace_globalOperator_eq_sum_localTerm [IsProper c.c₂.left]
    (F : c.FixedLocus) [IsProper F.F.hom]
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)]
    {ι : Type*} [Fintype ι] (B : ι → Over (Spec (.of k))) [∀ i, QuasiCompact (B i).hom]
    [∀ i, IsProper (B i).hom] (j : ∀ i, B i ⟶ F.F) [∀ i, IsOpenImmersion (j i).left]
    [∀ i, IsClosedImmersion (j i).left]
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).left.base)
      (Set.range (j i').left.base))
    (hcover : ⋃ i, Set.range (j i).left.base = Set.univ) :
    End.of (trace c.globalOperator) = ∑ i, (c.traceClass F).localTerm (j i) := by
  rw [c.trace_globalOperator_eq_integral_traceClass F,
    BorelMooreSection.integral_eq_sum_localTerm B j hdisj hcover]
end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
