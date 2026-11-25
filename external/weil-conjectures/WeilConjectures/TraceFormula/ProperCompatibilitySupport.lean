/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ConjugateComp
public import WeilConjectures.TraceFormula.ProperCompatibilityExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.TraceFormula.ShriekTrace

/-!

# Exchange of the support isomorphisms along a proper pushforward diagram

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with induced map of fixed loci `h`,
the support isomorphisms are exchanged by the exchange map `E` of the support square:
`Rb^!(RΔ_{Y*} τ_f) ∘ E ∘ Rg_* ζ_c = ζ_b ∘ Ri_{b*} τ_h`
(`Correspondence.ProperPushforwardDiagram.lowerStar_map_supportIso_comp_exchange`, blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, (2)). Following the blueprint proof, we pass to
the `Rb_! ⊣ Rb^!` adjoints; the exceptional adjoint of `ζ_c` is the composition law of the fixed
square followed by the trace `t_d`
(`ProEtale.CondensedRing.Correspondence.FixedLocus.homEquiv_symm_supportIso_hom`, the last
assertion of `theorem-proper-pushforward-lefschetz-verdier--1`), and the claim reduces to the
compatibility of the traces with composition
(`ProEtale.CondensedRing.lowerShriekSquareIso_trace_exchange`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.FixedLocus

variable {c : Correspondence ℓ K} (F : c.FixedLocus)

/-- **The exceptional adjoint of the support isomorphism** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 8, last assertion): the
`Rc_! ⊣ Rc^!`-adjoint of `ζ_c : Rι_* ω_Fix(c) ⟶ Rc^! RΔ_* ω_X` is
`Rc_! Rι_* ω ≅ Rc_! Rι_! ω ≅ RΔ_! Rd_! ω ⟶ RΔ_! ω_X ≅ RΔ_* ω_X`, the composition law of the
fixed square followed by the trace `t_d`. -/
theorem homEquiv_symm_supportIso_hom :
    ((boundedConstructibleUpperShriekAdjunction ℓ c.support).homEquiv _ _).symm
        F.supportIso.hom =
      (boundedConstructibleLowerShriek ℓ c.support).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι).inv.app
            (dualizingComplex' ℓ F.F)) ≫
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support).hom.app
          (dualizingComplex' ℓ F.F) ≫
        (boundedConstructibleLowerShriek ℓ (diag X)).map
          (lowerShriekDualizingComplexTrace ℓ F.d) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X)).hom.app
          (dualizingComplex' ℓ X) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback
  have hK := Adjunction.homEquiv_symm_conjugateIsoEquiv_inv_app
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (diag X))
    (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction ℓ F.d)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback)
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ F.isPullback)
    (dualizingComplex' ℓ X)
  simp only [supportIso, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Adjunction.homEquiv_naturality_left_symm, upperShriekLowerStarIso,
    lowerShriekBaseChangeIso, hK, lowerShriekDualizingComplexTrace,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_app_comp_map_map_assoc
    (boundedConstructibleLowerShriek ℓ c.support)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ F.ι).inv
    (dualizingComplexComp ℓ F.d).inv]
  have n := (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ F.ι_support).hom.naturality
    (dualizingComplexComp ℓ F.d).inv
  simp only [Functor.comp_map] at n
  simp only [reassoc_of% n]

end Correspondence.FixedLocus

section Exchange

variable (ℓ) {Fc Cc Xc Pc Fb Cb Yb Pb : Over (Spec (.of k))}
  [LocallyOfFiniteType Fc.hom] [QuasiCompact Fc.hom] [IsSeparated Fc.hom]
  [LocallyOfFiniteType Cc.hom] [QuasiCompact Cc.hom] [IsSeparated Cc.hom]
  [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom] [IsSeparated Xc.hom]
  [LocallyOfFiniteType Pc.hom] [QuasiCompact Pc.hom] [IsSeparated Pc.hom]
  [LocallyOfFiniteType Fb.hom] [QuasiCompact Fb.hom] [IsSeparated Fb.hom]
  [LocallyOfFiniteType Cb.hom] [QuasiCompact Cb.hom] [IsSeparated Cb.hom]
  [LocallyOfFiniteType Yb.hom] [QuasiCompact Yb.hom] [IsSeparated Yb.hom]
  [LocallyOfFiniteType Pb.hom] [QuasiCompact Pb.hom] [IsSeparated Pb.hom]
  {ιc : Fc ⟶ Cc} {c : Cc ⟶ Pc} {dc : Fc ⟶ Xc} {Δc : Xc ⟶ Pc}
  {ιb : Fb ⟶ Cb} {b : Cb ⟶ Pb} {db : Fb ⟶ Yb} {Δb : Yb ⟶ Pb}
  {g : Cc ⟶ Cb} {q : Pc ⟶ Pb} {f : Xc ⟶ Yb} {h : Fc ⟶ Fb}
  [IsProper ιc.left] [IsProper Δc.left] [IsProper ιb.left] [IsProper Δb.left] [IsProper g.left]
  [IsProper q.left] [IsProper f.left] [IsProper h.left] [IsProper (ιc ≫ g).left]
  [IsProper (h ≫ ιb).left] [IsProper (Δc ≫ q).left] [IsProper (f ≫ Δb).left]

lemma lowerStarDualizingComplexTrace_eq (a : Xc ⟶ Yb) [IsProper a.left] :
    lowerStarDualizingComplexTrace ℓ a =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).inv.app _ ≫
        lowerShriekDualizingComplexTrace ℓ a := by
  rw [lowerStarDualizingComplexTrace, lowerShriekDualizingComplexTrace]

/-- The exchange of the support isomorphisms along a map of squares, in terms of the
exceptional adjoints of the support isomorphisms (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, (2), proof): the two maps
`Rb_! Rg_* Rιc_* ω ⟶ RΔb_* ω` agree. -/
theorem lowerStar_square_trace_exchange (wc : ιc ≫ c = dc ≫ Δc) (wb : ιb ≫ b = db ≫ Δb)
    (wgb : g ≫ b = c ≫ q) (wq : Δc ≫ q = f ≫ Δb) (wh : ιc ≫ g = h ≫ ιb)
    (whd : dc ≫ f = h ≫ db) :
    (lowerStarLowerShriekCompIso ℓ wgb).hom.app
        ((boundedConstructibleLowerStar ℓ ιc).obj (dualizingComplex' ℓ Fc)) ≫
      (boundedConstructibleLowerStar ℓ q).map
        ((boundedConstructibleLowerShriek ℓ c).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ιc).inv.app
              (dualizingComplex' ℓ Fc)) ≫
          (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wc).hom.app
            (dualizingComplex' ℓ Fc) ≫
          (boundedConstructibleLowerShriek ℓ Δc).map (lowerShriekDualizingComplexTrace ℓ dc) ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δc).hom.app
            (dualizingComplex' ℓ Xc)) ≫
      (boundedConstructibleLowerStarComp ℓ Δc q).hom.app (dualizingComplex' ℓ Xc) ≫
      eqToHom (by rw [wq]) ≫
      (boundedConstructibleLowerStarComp ℓ f Δb).inv.app (dualizingComplex' ℓ Xc) ≫
      (boundedConstructibleLowerStar ℓ Δb).map (lowerStarDualizingComplexTrace ℓ f) =
    (boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerStarComp ℓ ιc g).hom.app (dualizingComplex' ℓ Fc) ≫
          eqToHom (by rw [wh]) ≫
          (boundedConstructibleLowerStarComp ℓ h ιb).inv.app (dualizingComplex' ℓ Fc) ≫
          (boundedConstructibleLowerStar ℓ ιb).map (lowerStarDualizingComplexTrace ℓ h)) ≫
      (boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ιb).inv.app
          (dualizingComplex' ℓ Fb)) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wb).hom.app (dualizingComplex' ℓ Fb) ≫
      (boundedConstructibleLowerShriek ℓ Δb).map (lowerShriekDualizingComplexTrace ℓ db) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δb).hom.app
        (dualizingComplex' ℓ Yb) := by
  simp only [lowerStarLowerShriekCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app, lowerStarComp_hom_app_eq,
    lowerStarComp_inv_app_eq, lowerStarDualizingComplexTrace_eq, Functor.map_comp,
    Category.assoc]
  simp only [Functor.map_hom_app_comp_map_inv_app_assoc (boundedConstructibleLowerStar ℓ q)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δc),
    Functor.map_hom_app_comp_map_inv_app_assoc (boundedConstructibleLowerStar ℓ Δb)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f),
    Functor.map_map_hom_app_comp_map_map_inv_app_assoc (boundedConstructibleLowerShriek ℓ b)
      (boundedConstructibleLowerStar ℓ ιb)
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h),
    lowerShriekIsoLowerStar_hom_app_comp_eqToHom_assoc ℓ wq, Iso.hom_inv_id_app_assoc,
    ← (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ Δb).hom.naturality
      (lowerShriekDualizingComplexTrace ℓ f)]
  simp only [Iso.hom_app_comp_map₃_comp_inv_app_assoc
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ q),
    Functor.map_hom_app_comp_map_map_comp_map_inv_app_assoc (boundedConstructibleLowerShriek ℓ b)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ ιb),
    ← Functor.map_comp_assoc (boundedConstructibleLowerShriek ℓ b)
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (ιc ≫ g)).hom.app _)]
  simp only [lowerShriekIsoLowerStar_hom_app_comp_eqToHom ℓ wh, Functor.map_comp_assoc,
    Functor.map_hom_app_comp_map_inv_app_assoc (boundedConstructibleLowerShriek ℓ b)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (h ≫ ιb)),
    NatTrans.app_comp_map_map_assoc (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom,
    ← lowerShriek_map_comp_eqToHom_assoc ℓ wgb,
    ← NatTrans.map_map_comp_app_assoc (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv,
    Functor.map_app_comp_map_map_assoc (boundedConstructibleLowerShriek ℓ b)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv,
    lowerShriekSquareIso_trace_exchange_assoc ℓ wc wb wgb wq wh whd]

end Exchange

namespace Correspondence.ProperPushforwardDiagram

variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)
  (Fc : c.FixedLocus) (Fb : P.pushforward.FixedLocus)

/-- **Exchange of the support isomorphisms** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, (2)):
`Rb^!(RΔ_{Y*} τ_f) ∘ E ∘ Rg_* ζ_c = ζ_b ∘ Ri_{b*} τ_h`, read through `g ∘ i_c = i_b ∘ h`. -/
theorem lowerStar_map_supportIso_comp_exchange :
    (boundedConstructibleLowerStar ℓ P.g).map Fc.supportIso.hom ≫
        (lowerStarUpperShriekExchange ℓ P.g_comp_support).app
          ((boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X)) ≫
        (boundedConstructibleUpperShriek ℓ P.pushforward.support).map
          ((boundedConstructibleLowerStarComp ℓ (diag X) (prod.map P.f P.f)).hom.app
              (dualizingComplex' ℓ X) ≫
            eqToHom (by rw [P.diag_comp_prodMap]) ≫
            (boundedConstructibleLowerStarComp ℓ P.f (diag Y)).inv.app
              (dualizingComplex' ℓ X) ≫
            (boundedConstructibleLowerStar ℓ (diag Y)).map
              (lowerStarDualizingComplexTrace ℓ P.f)) =
      (boundedConstructibleLowerStarComp ℓ Fc.ι P.g).hom.app (dualizingComplex' ℓ Fc.F) ≫
        eqToHom (by rw [← P.fixMap_ι]) ≫
        (boundedConstructibleLowerStarComp ℓ (P.fixMap Fc Fb) Fb.ι).inv.app
          (dualizingComplex' ℓ Fc.F) ≫
        (boundedConstructibleLowerStar ℓ Fb.ι).map
          (lowerStarDualizingComplexTrace ℓ (P.fixMap Fc Fb)) ≫
        Fb.supportIso.hom := by
  have whd : Fc.d ≫ P.f = P.fixMap Fc Fb ≫ Fb.d := by
    rw [Correspondence.FixedLocus.d, Correspondence.FixedLocus.d, Category.assoc,
      P.fixMap_ι_b₁]
  have : IsProper (Fc.ι ≫ P.g).left := inferInstanceAs (IsProper (Fc.ι.left ≫ P.g.left))
  have : IsProper (P.fixMap Fc Fb ≫ Fb.ι).left :=
    inferInstanceAs (IsProper ((P.fixMap Fc Fb).left ≫ Fb.ι.left))
  have : IsProper (diag X ≫ prod.map P.f P.f).left :=
    inferInstanceAs (IsProper ((diag X).left ≫ (prod.map P.f P.f).left))
  have : IsProper (P.f ≫ diag Y).left := inferInstanceAs (IsProper (P.f.left ≫ (diag Y).left))
  apply ((boundedConstructibleUpperShriekAdjunction ℓ P.pushforward.support).homEquiv _
    _).symm.injective
  have hm := Adjunction.homEquiv_comp_mateEquiv
    (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction ℓ P.pushforward.support)
    (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom (𝟙 _) Fc.supportIso.hom
    ((boundedConstructibleLowerStarComp ℓ (diag X) (prod.map P.f P.f)).hom.app
        (dualizingComplex' ℓ X) ≫
      eqToHom (by rw [P.diag_comp_prodMap]) ≫
      (boundedConstructibleLowerStarComp ℓ P.f (diag Y)).inv.app (dualizingComplex' ℓ X) ≫
      (boundedConstructibleLowerStar ℓ (diag Y)).map (lowerStarDualizingComplexTrace ℓ P.f))
  simp only [Category.id_comp] at hm
  simp only [lowerStarUpperShriekExchange, ← hm, Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_naturality_left_symm]
  simp only [Fc.homEquiv_symm_supportIso_hom, Fb.homEquiv_symm_supportIso_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have key := lowerStar_square_trace_exchange ℓ Fc.ι_support Fb.ι_support P.g_comp_support
    P.diag_comp_prodMap (P.fixMap_ι Fc Fb).symm whd
  simp only [Functor.map_comp, Category.assoc] at key ⊢
  exact key

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
