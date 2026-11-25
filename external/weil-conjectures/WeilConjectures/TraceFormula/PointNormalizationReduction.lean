/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.TraceFormula.SupportedClass

/-!

# Point normalization of the trace class: reduction to a coevaluation

Over the base point `s = Spec k`, the integral `∫_s Tr(v)` of the trace class of the diagonal
correspondence of an endomorphism `v` is `P ∘ (v ⊗ D_s K) ∘ σ`
(`ProEtale.CondensedRing.Correspondence.integral_traceClass_ofEnd_eq`), for the coevaluation
`σ = pointCoev v : ℚ̄_ℓ ⟶ K ⊗ D_s K` built from the class of the identity and the pairing
`P = pointPairing v`, the evaluation followed by `ω_s ≅ ℚ̄_ℓ` (blueprint
`lemma-local-terms-point--1`). The coevaluation is written as
`σ = (eB ⊗ eC) ∘ δ ∘ LΔ^* (κ⁻¹ ∘ [1]) ∘ τ` (`ProEtale.CondensedRing.Correspondence.pointCoev_eq`),
with the identifications `LΔ^* Lp^* ≅ 𝟭` of `diagUpperStarProjIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Verdier

/-- Abstract form of the reduction of the integral of the trace class of a diagonal
correspondence: the exceptional adjoint along `d` of `b ≫ G (A ≫ B) ≫ dI ≫ e`, read through
`ψ : R ≅ 𝟭`, with `G B ≫ dI = dI ≫ (v ▷ D)`. -/
lemma integral_traceClass_aux {Cs CP : Type*} [Category Cs] [MonoidalCategory Cs] [Category CP]
    {G : CP ⥤ Cs} {Lf R : Cs ⥤ Cs} (adj : Lf ⊣ R) (ψ : R ≅ 𝟭 Cs) {T E : CP} {U' : Cs}
    {K D ω ω' : Cs} (ε : 𝟙_ Cs ⟶ U') (b : Lf.obj U' ⟶ G.obj T) (sc A : T ⟶ E) (B : E ⟶ E)
    (hsc : sc = A ≫ B) (dI : G.obj E ⟶ K ⊗ D) (v : K ⟶ K)
    (hB : G.map B ≫ dI = dI ≫ v ▷ D) (e : K ⊗ D ⟶ ω) (d₁ : R.obj ω ⟶ ω') (d₂ : ω' ⟶ 𝟙_ Cs) :
    (ε ≫ adj.homEquiv _ _ (b ≫ G.map sc ≫ dI ≫ e) ≫ d₁) ≫ d₂ =
      (ε ≫ adj.unit.app U' ≫ R.map (b ≫ G.map A ≫ dI) ≫ ψ.hom.app _) ≫ v ▷ D ≫
        (e ≫ ψ.inv.app ω ≫ d₁ ≫ d₂) := by
  subst hsc
  rw [Adjunction.homEquiv_unit, G.map_comp]
  simp only [Category.assoc, reassoc_of% hB]
  rw [show b ≫ G.map A ≫ dI ≫ v ▷ D ≫ e = (b ≫ G.map A ≫ dI) ≫ (v ▷ D ≫ e) by
    simp only [Category.assoc], R.map_comp, ← NatIso.naturality_2 ψ (v ▷ D ≫ e)]
  simp only [Functor.id_map, Category.assoc]

/-- Abstract form of the naturality of the identification `LΔ^* (K ⊠ N) ≅ K ⊗ N` in `K`. -/
lemma diagIso_naturality_aux {Cs CP : Type*} [Category Cs] [MonoidalCategory Cs] [Category CP]
    [MonoidalCategory CP] (G : CP ⥤ Cs) [G.Monoidal] {A A' Y : CP} {K K' N : Cs} (a : A ⟶ A')
    (k : K ⟶ K') (e₁ : G.obj A ⟶ K) (e₁' : G.obj A' ⟶ K') (e₂ : G.obj Y ⟶ N)
    (he : G.map a ≫ e₁' = e₁ ≫ k) :
    G.map (a ▷ Y) ≫ Functor.OplaxMonoidal.δ G A' Y ≫ (e₁' ⊗ₘ e₂) =
      (Functor.OplaxMonoidal.δ G A Y ≫ (e₁ ⊗ₘ e₂)) ≫ k ▷ N := by
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, Category.assoc, ← tensorHom_id,
    ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, he, Category.id_comp,
    Category.comp_id]

end CategoryTheory.Verdier

namespace CategoryTheory.Verdier

/-- An algebraic step of `diagUpperStarProjIso_tensor`. -/
lemma tensor_comp_iso_aux {C : Type*} [Category C] [MonoidalCategory C]
    {QML QM QL RML RM RL IML IM IL
    KM KL : C} (cML : QML ≅ RML) (cM : QM ≅ RM) (cL : QL ≅ RL) (eML : QML ⟶ IML) (eM : QM ⟶ IM)
    (eL : QL ⟶ IL) (sML : IML ⟶ KM ⊗ KL) (sM : IM ⟶ KM) (sL : IL ⟶ KL) {RML' : C} (x₁ : RML ⟶ RML')
    (x₂ : RML' ⟶ RM ⊗ RL) (y : QML ⟶ QM ⊗ QL) (z : IML ⟶ IM ⊗ IL)
    (h₁ : y ≫ (cM.hom ⊗ₘ cL.hom) = cML.hom ≫ x₁ ≫ x₂)
    (h₂ : y ≫ (eM ⊗ₘ eL) = eML ≫ z) (h₃ : z ≫ (sM ⊗ₘ sL) = sML) :
    x₁ ≫ x₂ ≫ ((cM.inv ≫ eM ≫ sM) ⊗ₘ (cL.inv ≫ eL ≫ sL)) = cML.inv ≫ eML ≫ sML := by
  rw [← cancel_epi cML.hom, Iso.hom_inv_id_assoc, ← Category.assoc x₁, ← Category.assoc,
    ← h₁, Category.assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, ← tensorHom_comp_tensorHom, reassoc_of% h₂, h₃]

/-- An algebraic step of `diagUpperStarProjIso_μ_map`. -/
lemma μ_map_aux {P S : Type*} [Category P] [Category S] [MonoidalCategory P] [MonoidalCategory S]
    (F : P ⥤ S) [F.Monoidal] (G : S ⥤ P) [G.Monoidal] (e : ∀ X, F.obj (G.obj X) ⟶ X) {M L Z : S}
    (g : M ⊗ L ⟶ Z) (hnat : F.map (G.map g) ≫ e Z = e (M ⊗ L) ≫ g)
    (htens : F.map (Functor.OplaxMonoidal.δ G M L) ≫ Functor.OplaxMonoidal.δ F _ _ ≫
      (e M ⊗ₘ e L) = e (M ⊗ L)) :
    Functor.LaxMonoidal.μ F _ _ ≫ F.map (Functor.LaxMonoidal.μ G M L) ≫ F.map (G.map g) ≫ e Z =
      (e M ⊗ₘ e L) ≫ g := by
  rw [hnat, ← htens]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ, Functor.map_id, Category.id_comp,
    Functor.Monoidal.μ_δ_assoc]

/-- The uncurried form of `Cl = A ≫ curry p`. -/
lemma whiskerLeft_comp_inv_curry {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
    {M X Y N : C} (Cl : X ⟶ (ihom M).obj N) (p : M ⊗ Y ⟶ N) (_ : IsIso (MonoidalClosed.curry p)) :
    M ◁ (Cl ≫ inv (MonoidalClosed.curry p)) ≫ p = MonoidalClosed.uncurry Cl := by
  calc M ◁ (Cl ≫ inv (MonoidalClosed.curry p)) ≫ p =
        M ◁ (Cl ≫ inv (MonoidalClosed.curry p)) ≫
          MonoidalClosed.uncurry (MonoidalClosed.curry p) := by
        rw [MonoidalClosed.uncurry_curry]
    _ = MonoidalClosed.uncurry ((Cl ≫ inv (MonoidalClosed.curry p)) ≫
          MonoidalClosed.curry p) := (MonoidalClosed.uncurry_natural_left _ _).symm
    _ = MonoidalClosed.uncurry Cl := by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- An algebraic step of `pointClass_coeff`. -/
lemma coeff_cancel_aux {C : Type*} [Category C] {X₁ X₂ X₃ K Y Z W : C} (a : X₁ ⟶ X₂)
    (e₁ : X₂ ⟶ X₃) (s : X₃ ⟶ K) (t : Y ≅ K) (e₂ : Y ⟶ Z) (e₃ : Z ⟶ Y) (he : e₂ ≫ e₃ = 𝟙 _)
    (u : Z ≅ W) :
    (a ≫ (e₁ ≫ (s ≫ t.inv) ≫ e₂) ≫ u.hom) ≫ u.inv ≫ e₃ ≫ t.hom = a ≫ e₁ ≫ s := by
  simp [reassoc_of% he]

/-- Commuting a natural isomorphism `ψ : R ≅ 𝟭` past `R.map x`. -/
lemma comp_map_comp_iso_hom_app {C : Type*} [Category C] {R : C ⥤ C} (ψ : R ≅ 𝟭 C) {V W X Y : C}
    (a₁ : V ⟶ W) (a₂ : W ⟶ R.obj X) (x : X ⟶ Y) :
    a₁ ≫ a₂ ≫ R.map x ≫ ψ.hom.app Y = (a₁ ≫ a₂ ≫ ψ.hom.app X) ≫ x := by
  rw [ψ.hom.naturality x, Functor.id_map]
  simp only [Category.assoc]

/-- A naturality square for a composite of three morphisms. -/
lemma comp_comp_naturality {𝒞 : Type*} [Category 𝒞] {A A' B B' C C' D D' : 𝒞} {x : A ⟶ A'}
    {y : B ⟶ B'} {z : C ⟶ C'} {w : D ⟶ D'} {c : A ⟶ B} {c' : A' ⟶ B'} {e : B ⟶ C}
    {e' : B' ⟶ C'} {s : C ⟶ D} {s' : C' ⟶ D'} (h₁ : x ≫ c' = c ≫ y) (h₂ : y ≫ e' = e ≫ z)
    (h₃ : z ≫ s' = s ≫ w) :
    x ≫ c' ≫ e' ≫ s' = (c ≫ e ≫ s) ≫ w := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

end CategoryTheory.Verdier

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Naturality

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

lemma upperStar_map_comp_eqToHom_of_eq {f g : X ⟶ X} (h : f = g)
    {L L' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L') :
    (boundedConstructibleUpperStar _ ℓ f).map b ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (boundedConstructibleUpperStar _ ℓ g).map b := by
  subst h
  simp

variable (ℓ) in
/-- The identification `LΔ^* (K ⊠ N) ≅ K ⊗ N` is natural in `K`. -/
lemma diagUpperStarExternalProductIso_hom_naturality
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (v : K ⟶ K') (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).map v ▷
          (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj N) ≫
        (diagUpperStarExternalProductIso ℓ K' N).hom =
      (diagUpperStarExternalProductIso ℓ K N).hom ≫ v ▷ N := by
  have h₁ := (boundedConstructibleUpperStarComp _ ℓ (diag X) prod.fst).inv.naturality v
  have h₂ := upperStar_map_comp_eqToHom_of_eq (ℓ := ℓ)
    (show diag X ≫ prod.fst = 𝟙 X by simp) v
  have h₃ := (boundedConstructibleUpperStarId _ ℓ X).hom.naturality v
  have h₄ := Verdier.comp_comp_naturality h₁ h₂ h₃
  have h₅ := Verdier.diagIso_naturality_aux (boundedConstructibleUpperStar _ ℓ (diag X))
    (Y := (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj N) _ v _ _
    ((boundedConstructibleUpperStarComp _ ℓ (diag X) prod.snd).inv.app N ≫
      eqToHom (by rw [diag, prod.lift_snd]) ≫ (boundedConstructibleUpperStarId _ ℓ X).hom.app N)
    h₄
  simp only [diagUpperStarExternalProductIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Functor.Monoidal.μIso_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom]
  convert h₅ using 4
  all_goals rfl

end Naturality

namespace Correspondence

variable {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}

lemma fixedLocusOfEnd_d (v : K ⟶ K) : (fixedLocusOfEnd v).d = 𝟙 (point k) :=
  Category.comp_id _

/-- The identification `Rd^! ≅ 𝟭` for the map `d = 𝟙` of the fixed square of a diagonal
correspondence over the base point. -/
noncomputable def fixedLocusOfEndUpperShriekIso (v : K ⟶ K) :
    boundedConstructibleUpperShriek ℓ (fixedLocusOfEnd v).d ≅
      𝟭 _ :=
  eqToIso (by rw [fixedLocusOfEnd_d]) ≪≫ boundedConstructibleUpperShriekId ℓ (point k)

/-- The coevaluation `σ : ℚ̄_ℓ ⟶ K ⊗ D_s K` through which the trace class of the diagonal
correspondence of `v` over the base point is computed: the adjoint along the fixed locus of
`LΔ^*` of the class of the identity read through `κ⁻¹`. -/
noncomputable def pointCoev (v : K ⟶ K) :
    𝟙_ _ ⟶ K ⊗ verdierDual ℓ K :=
  (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (fixedLocusOfEnd v).ι)).hom ≫
    (boundedConstructibleUpperShriekAdjunction ℓ (fixedLocusOfEnd v).d).unit.app _ ≫
    (boundedConstructibleUpperShriek ℓ (fixedLocusOfEnd v).d).map
      ((fixedLocusOfEnd v).lowerShriekBaseChangeIso.inv.app (𝟙_ _) ≫
        (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
          (diagUnitClass ℓ (ofEnd K v).support_snd (ofEnd K v).support_fst.symm ≫
            inv (kunnethVerdierMap ℓ K K)) ≫
        (diagUpperStarExternalProductIso ℓ K _).hom) ≫
    (fixedLocusOfEndUpperShriekIso v).hom.app _

/-- The pairing `P : K ⊗ D_s K ⟶ ℚ̄_ℓ` through which the trace class of the diagonal
correspondence of `v` over the base point is computed: the evaluation followed by
`ω_s ≅ ℚ̄_ℓ`. -/
noncomputable def pointPairing (v : K ⟶ K) :
    K ⊗ verdierDual ℓ K ⟶ 𝟙_ _ :=
  (ihom.ev K).app (dualizingComplex' ℓ (point k)) ≫
    (fixedLocusOfEndUpperShriekIso v).inv.app _ ≫
    (dualizingComplexComp ℓ (fixedLocusOfEnd v).d).hom ≫ (dualizingComplexPointIso ℓ k).hom

/-- **The integral of the trace class of a diagonal correspondence over the base point** is
`P ∘ (v ⊗ D_s K) ∘ σ`. -/
theorem integral_traceClass_ofEnd_eq (v : K ⟶ K) :
    ((ofEnd K v).traceClass (fixedLocusOfEnd v)).integral =
      .of (pointCoev v ≫ v ▷ _ ≫ pointPairing v) := by
  rw [BorelMooreSection.integral_point, traceClass_eq_homEquiv]
  apply End.ext
  have h := Verdier.integral_traceClass_aux
    (G := boundedConstructibleUpperStar _ ℓ (diag (point k)))
    (T := (boundedConstructibleLowerShriek ℓ (ofEnd K v).support).obj (𝟙_ _))
    (boundedConstructibleUpperShriekAdjunction ℓ (fixedLocusOfEnd v).d)
    (fixedLocusOfEndUpperShriekIso v)
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (fixedLocusOfEnd v).ι)).hom
    ((fixedLocusOfEnd v).lowerShriekBaseChangeIso.inv.app (𝟙_ _)) _ _ _
    (supportedClass_ofEnd ℓ v) (diagUpperStarExternalProductIso ℓ K _).hom v
    (diagUpperStarExternalProductIso_hom_naturality ℓ v _)
    ((ihom.ev K).app (dualizingComplex' ℓ (point k)))
    (dualizingComplexComp ℓ (fixedLocusOfEnd v).d).hom (dualizingComplexPointIso ℓ k).hom
  convert h using 2 <;> rfl

variable (ℓ) in
/-- The identification `LΔ^* Lp^* M ≅ M` along `Δ ≫ p = 𝟙` for a projection `p` of `s ⨯ s`. -/
noncomputable def diagUpperStarProjIso (p : point k ⨯ point k ⟶ point k)
    (hp : diag (point k) ≫ p = 𝟙 _)
    (M : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag (point k))).obj
        ((boundedConstructibleUpperStar _ ℓ p).obj M) ≅ M :=
  ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) p).app M).symm ≪≫
    eqToIso (by rw [hp]) ≪≫ (boundedConstructibleUpperStarId _ ℓ (point k)).app M

lemma upperStar_δ_eqToHom {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] {f g : point k ⟶ Y} (h : f = g)
    (M L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ f) M L ≫
        (eqToHom (congrArg (fun φ ↦ (boundedConstructibleUpperStar _ ℓ φ).obj M) h) ⊗ₘ
          eqToHom (congrArg (fun φ ↦ (boundedConstructibleUpperStar _ ℓ φ).obj L) h)) =
      eqToHom (congrArg (fun φ ↦ (boundedConstructibleUpperStar _ ℓ φ).obj (M ⊗ L)) h) ≫
        Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ g) M L := by
  subst h
  simp

variable (ℓ) in
/-- The identification `LΔ^* Lp^* ≅ 𝟭` is monoidal. -/
lemma diagUpperStarProjIso_tensor (p : point k ⨯ point k ⟶ point k)
    (hp : diag (point k) ≫ p = 𝟙 _) (M L : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
        (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ p) M L) ≫
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ (diag (point k))) _ _ ≫
      ((diagUpperStarProjIso ℓ p hp M).hom ⊗ₘ (diagUpperStarProjIso ℓ p hp L).hom) =
    (diagUpperStarProjIso ℓ p hp (M ⊗ L)).hom := by
  have h₁ := boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ (diag (point k)) p M L
  have h₂ := upperStar_δ_eqToHom (ℓ := ℓ) hp M L
  have h₃ := boundedConstructibleUpperStarId_hom_app_tensor_δ ℓ (point k) M L
  refine Verdier.tensor_comp_iso_aux (C := Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) p).app (M ⊗ L))
    ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) p).app M)
    ((boundedConstructibleUpperStarComp _ ℓ (diag (point k)) p).app L) _ _ _ _ _ _ _ _
    (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ (diag (point k) ≫ p)) M L)
    (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ (𝟙 (point k))) M L) ?_ ?_ ?_
  · convert h₁ using 2 <;> rfl
  · convert h₂ using 2 <;> simp only [eqToIso.hom]
  · convert h₃ using 2 <;> rfl

variable (ℓ) in
/-- The identification `LΔ^* Lp^* ≅ 𝟭` is natural. -/
lemma diagUpperStarProjIso_naturality (p : point k ⨯ point k ⟶ point k)
    (hp : diag (point k) ≫ p = 𝟙 _) {M M' : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (g : M ⟶ M') :
    (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
        ((boundedConstructibleUpperStar _ ℓ p).map g) ≫ (diagUpperStarProjIso ℓ p hp M').hom =
      (diagUpperStarProjIso ℓ p hp M).hom ≫ g := by
  have h₁ := (boundedConstructibleUpperStarComp _ ℓ (diag (point k)) p).inv.naturality g
  have h₂ := upperStar_map_comp_eqToHom_of_eq (ℓ := ℓ) hp g
  have h₃ := (boundedConstructibleUpperStarId _ ℓ (point k)).hom.naturality g
  simp only [diagUpperStarProjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    eqToIso.hom]
  exact Verdier.comp_comp_naturality h₁ h₂ h₃

variable (ℓ) in
/-- The identification `LΔ^* Lp^* ≅ 𝟭` is compatible with the tensor structures and the image of
a map out of a tensor product. -/
lemma diagUpperStarProjIso_μ_map (p : point k ⨯ point k ⟶ point k)
    (hp : diag (point k) ≫ p = 𝟙 _) (M L Z : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : M ⊗ L ⟶ Z) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (diag (point k))) _ _ ≫
        (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
          (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ p) M L) ≫
        (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
          ((boundedConstructibleUpperStar _ ℓ p).map g) ≫ (diagUpperStarProjIso ℓ p hp Z).hom =
      ((diagUpperStarProjIso ℓ p hp M).hom ⊗ₘ (diagUpperStarProjIso ℓ p hp L).hom) ≫ g := by
  exact Verdier.μ_map_aux _ _ (fun X ↦ (diagUpperStarProjIso ℓ p hp X).hom) g
    (diagUpperStarProjIso_naturality ℓ p hp g) (diagUpperStarProjIso_tensor ℓ p hp M L)

omit [Fact (ringChar k).Prime] in
lemma diag_point_fst : diag (point k) ≫ (prod.fst : point k ⨯ point k ⟶ point k) = 𝟙 _ := by
  simp

omit [Fact (ringChar k).Prime] in
lemma diag_point_snd : diag (point k) ≫ (prod.snd : point k ⨯ point k ⟶ point k) = 𝟙 _ := by
  simp

/-- The point `τ : ℚ̄_ℓ ⟶ LΔ^* RΔ_! ℚ̄_ℓ` through which the coevaluation over the base point
factors. -/
noncomputable def pointTau (v : K ⟶ K) :
    𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      (boundedConstructibleUpperStar _ ℓ (diag (point k))).obj
      ((boundedConstructibleLowerShriek ℓ (diag (point k))).obj (𝟙_ _)) :=
  (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (fixedLocusOfEnd v).ι)).hom ≫
    (boundedConstructibleUpperShriekAdjunction ℓ (fixedLocusOfEnd v).d).unit.app _ ≫
    (fixedLocusOfEndUpperShriekIso v).hom.app _ ≫
    (fixedLocusOfEnd v).lowerShriekBaseChangeIso.inv.app (𝟙_ _)

lemma pointCoev_eq (v : K ⟶ K) :
    pointCoev v = pointTau v ≫ (boundedConstructibleUpperStar _ ℓ (diag (point k))).map
        (diagUnitClass ℓ (K := K) diag_point_snd diag_point_fst.symm ≫
          inv (kunnethVerdierMap ℓ K K)) ≫
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ (diag (point k))) _ _ ≫
      ((diagUpperStarProjIso ℓ prod.fst (by simp) K).hom ⊗ₘ
        (diagUpperStarProjIso ℓ prod.snd (by simp) _).hom) := by
  unfold pointCoev
  refine (Verdier.comp_map_comp_iso_hom_app (fixedLocusOfEndUpperShriekIso v) _ _ _).trans ?_
  simp only [pointTau, Category.assoc]
  congr 4

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
