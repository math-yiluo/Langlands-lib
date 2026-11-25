/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ProperCompatibilityEvaluation
public import WeilConjectures.TraceFormula.ProperCompatibilitySupport
public import WeilConjectures.TraceFormula.SourceExchange

/-!

# Proper pushforward compatibility of the trace class

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with induced proper map of fixed
loci `h`, the Borel–Moore pushforward of the trace class of `u` is the trace class of the pushed
correspondence: `h_* Tr_c(u) = Tr_b([f, g]_! u)` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, `theorem-proper-pushforward-lefschetz-verdier`).
The proof goes through the exchange of the evaluation kernels along `f`
(`ProEtale.CondensedRing.kernelPushforward_comp_evaluationKernel_lowerStar`, blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, (1)), of the support isomorphisms
(`theorem-proper-pushforward-lefschetz-verdier--1`, (2)) and of the trace-class sources
(`theorem-proper-pushforward-lefschetz-verdier--1`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Bookkeeping for the proper pushforward of the trace class (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 4): two chains of points through a square
agree. -/
private lemma comp_eq_comp_of_points {C : Type*} [Category C]
    {P₀ P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ Q₃ Q₄ Q₅ R₁ R₂ S₁ S₂ N : C}
    (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (a₃ : P₂ ⟶ P₃) (a₄ : P₃ ⟶ P₄) (t : P₄ ⟶ P₅)
    (b₁ : P₀ ⟶ Q₁) (b₂ : Q₁ ⟶ Q₂) (b₃ : Q₂ ⟶ Q₃) (b₄ : Q₃ ⟶ Q₄) (t' : Q₄ ⟶ Q₅)
    (e₁ : Q₅ ⟶ R₁) (e₂ : R₁ ⟶ R₂) (e₃ : R₂ ⟶ P₅) (f₁ : Q₄ ⟶ S₁) (f₂ : S₁ ⟶ S₂) (f₃ : S₂ ⟶ P₄)
    (z : P₀ ⟶ S₁) (w : P₀ ⟶ S₂) (r : P₅ ⟶ N)
    (hnat : t' ≫ e₁ ≫ e₂ ≫ e₃ = f₁ ≫ f₂ ≫ f₃ ≫ t) (hpg : b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ f₁ = z)
    (htr : z ≫ f₂ = w) (hhb : a₁ ≫ a₂ ≫ a₃ ≫ a₄ = w ≫ f₃) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ t ≫ r = b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ t' ≫ e₁ ≫ e₂ ≫ e₃ ≫ r := by
  rw [reassoc_of% hnat]
  simp only [← Category.assoc] at hpg hhb ⊢
  rw [hpg, hhb, ← htr]

/-- Transporting a point and then a section through a naturality square agrees with
transporting their composite. The two composition isomorphisms cancel at the point. -/
private lemma comp_map_eq_of_point_square {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {I : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {J : C ⥤ D} {S T : A ⥤ D}
    (e : I ⋙ G ≅ S) (e' : H ⋙ J ≅ T)
    {U V : A} {oB : B} {oC : C} {oD : D} {N : C}
    {p : oB ⟶ I.obj U} {g : oD ⟶ G.obj oB}
    {h : oC ⟶ H.obj U} {b : oD ⟶ J.obj oC}
    {s : oD ⟶ S.obj U} {t : oD ⟶ T.obj U}
    (α : U ⟶ V) (τ : H.obj V ⟶ N) (fU : S.obj U ⟶ T.obj U) (fV : S.obj V ⟶ T.obj V)
    (hnat : S.map α ≫ fV = fU ≫ T.map α)
    (hpg : g ≫ G.map p = s ≫ e.inv.app U)
    (hhb : b ≫ J.map h = t ≫ e'.inv.app U) (htr : s ≫ fU = t) :
    b ≫ J.map (h ≫ H.map α ≫ τ) =
      g ≫ G.map (p ≫ I.map α) ≫ e.hom.app V ≫ fV ≫ e'.inv.app V ≫ J.map τ := by
  have n₁ := e.hom.naturality α
  have n₃ := e'.inv.naturality α
  simp only [Functor.comp_map] at n₁ n₃
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n₁, reassoc_of% hnat, reassoc_of% n₃, reassoc_of% hpg,
    Iso.inv_hom_id_app_assoc, reassoc_of% htr, reassoc_of% hhb]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.ProperPushforwardDiagram

variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y) (Fc : c.FixedLocus)
  (Fb : P.pushforward.FixedLocus)

/-- The point `T_b = 𝔱 ∘ ũ` of the pushed correspondence is obtained from that of `c` by
transport along `g` (blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 3):
`T_b = Ri_{b*} τ_h ∘ Rg_* T_c ∘ η_g`. -/
lemma mate_comp_traceMap_pushforward :
    P.pushforward.mate ≫ P.pushforward.traceMap Fb =
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).unit.app (𝟙_ _) ≫
          (boundedConstructibleLowerStar ℓ P.g).map
            (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv) ≫
        (boundedConstructibleLowerStar ℓ P.g).map (c.mate ≫ c.traceMap Fc) ≫
        (boundedConstructibleLowerStarComp ℓ Fc.ι P.g).hom.app (dualizingComplex' ℓ Fc.F) ≫
        eqToHom (by rw [← P.fixMap_ι]) ≫
        (boundedConstructibleLowerStarComp ℓ (P.fixMap Fc Fb) Fb.ι).inv.app
          (dualizingComplex' ℓ Fc.F) ≫
        (boundedConstructibleLowerStar ℓ Fb.ι).map
          (lowerStarDualizingComplexTrace ℓ (P.fixMap Fc Fb)) := by
  have e4 := Adjunction.homEquiv_comp_mateEquiv_of_eq
    (G := boundedConstructibleLowerStar ℓ P.g)
    (H := boundedConstructibleLowerStar ℓ (prod.map P.f P.f))
    (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction ℓ P.pushforward.support)
    (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar ℓ P.g).map
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv)
    c.kernelClass (evaluationKernel ℓ K)
    ((boundedConstructibleLowerStarComp ℓ (diag X) (prod.map P.f P.f)).hom.app
          (dualizingComplex' ℓ X) ≫
        eqToHom (by rw [P.diag_comp_prodMap]) ≫
        (boundedConstructibleLowerStarComp ℓ P.f (diag Y)).inv.app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (diag Y)).map (lowerStarDualizingComplexTrace ℓ P.f))
    (c.mate ≫ c.traceMap Fc) Fc.supportIso.hom
    (by rw [Category.assoc]; exact (mate_comp_traceMap_comp_supportIso c Fc).symm) _
    (lowerStarUpperShriekExchange ℓ P.g_comp_support)
    (by unfold lowerStarUpperShriekExchange; rfl)
    (P.lowerStar_map_supportIso_comp_exchange Fc Fb)
  have e1 := mate_comp_traceMap_comp_supportIso P.pushforward Fb
  rw [P.kernelClass_pushforward] at e1
  simp only [Category.assoc, P.kernelPushforward_comp_evaluationKernel] at e1
  have e5 := e1.trans e4
  rw [← cancel_mono Fb.supportIso.hom]
  simpa only [Category.assoc] using e5

/-- **Proper pushforward compatibility of the trace class** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, `theorem-proper-pushforward-lefschetz-verdier`;
Varshavsky 1.2.5): for a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with induced proper
map of fixed loci `h`, `h_* Tr_c(u) = Tr_b([f, g]_! u)`. No properness over `s` and no cartesian leg
square are needed. The special case `f = 𝟙` is blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`. The proof goes through the exchange of the trace
maps (`theorem-proper-pushforward-lefschetz-verdier--1`) and of the trace-class sources
(`theorem-proper-pushforward-lefschetz-verdier--1`). -/
theorem traceClassPushforward_eq :
    P.traceClassPushforward Fc Fb = P.pushforward.traceClass Fb := by
  have hTc : c.mate ≫ c.traceMap Fc =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ Fc.ι).homEquiv _ _
        ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ Fc.ι)).inv ≫
          c.traceClass Fc) := by
    rw [traceClass, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  have key : (boundedConstructibleUpperStarLowerStarAdjunction ℓ Fb.ι).homEquiv _ _
      ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ Fb.ι)).inv ≫
        P.traceClassPushforward Fc Fb) = P.pushforward.mate ≫ P.pushforward.traceMap Fb := by
    rw [P.mate_comp_traceMap_pushforward Fc Fb, hTc]
    have hpg := Adjunction.unit_map_comp_unit_map
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ Fc.ι)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (Fc.ι ≫ P.g))
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ Fc.ι P.g)
      (boundedConstructibleLowerStarComp ℓ Fc.ι P.g)
      rfl _ _ _ (boundedConstructibleUpperStarComp_hom_app_unit ℓ Fc.ι P.g)
    have hhb := Adjunction.unit_map_comp_unit_map
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (P.fixMap Fc Fb))
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ Fb.ι)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (P.fixMap Fc Fb ≫ Fb.ι))
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (P.fixMap Fc Fb) Fb.ι)
      (boundedConstructibleLowerStarComp ℓ
        (P.fixMap Fc Fb) Fb.ι)
      rfl _ _ _
      (boundedConstructibleUpperStarComp_hom_app_unit ℓ (P.fixMap Fc Fb) Fb.ι)
    have htr := unit_comp_map_εIso_inv_comp_eqToHom_of_eq (ℓ := ℓ) (P.fixMap_ι Fc Fb).symm
    have hn := lowerStar_map_comp_eqToHom_of_eq (ℓ := ℓ) (P.fixMap_ι Fc Fb).symm
      (c.traceClass Fc)
    have h := comp_map_eq_of_point_square
      (I := boundedConstructibleLowerStar ℓ Fc.ι)
      (G := boundedConstructibleLowerStar ℓ P.g)
      (H := boundedConstructibleLowerStar ℓ (P.fixMap Fc Fb))
      (J := boundedConstructibleLowerStar ℓ Fb.ι)
      (boundedConstructibleLowerStarComp ℓ Fc.ι P.g)
      (boundedConstructibleLowerStarComp ℓ (P.fixMap Fc Fb) Fb.ι)
      (c.traceClass Fc) (lowerStarDualizingComplexTrace ℓ (P.fixMap Fc Fb))
      _ _ hn hpg hhb htr
    simpa only [Adjunction.homEquiv_unit, traceClassPushforward, BorelMooreSection.pushforward,
      lowerStarDualizingComplexTrace, Functor.map_comp, Category.assoc] using h
  rw [traceClass, ← key, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
