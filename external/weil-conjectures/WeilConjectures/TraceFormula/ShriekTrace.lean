/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.Dualizing

/-!

# The trace of the dualizing complexes along the compactly supported direct image

For a morphism `a : A ⟶ B` of separated `k`-schemes of finite type, the *trace*
`t_a : Ra_! ω_A ⟶ ω_B` (`ProEtale.CondensedRing.lowerShriekDualizingComplexTrace`) is the
exceptional adjoint of `ω_A ≅ Ra^! ω_B`. Its adjoint along the structure morphism of `B` is the
composition isomorphism followed by the counit of `A`
(`ProEtale.CondensedRing.lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit`), and the
traces are compatible with composition: `t_{a ≫ b} = t_b ∘ Rb_! t_a`
(`ProEtale.CondensedRing.lowerShriekDualizingComplexTrace_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {A B C : Over (Spec (.of k))}
  [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]

/-- The *trace* `t_a : Ra_! ω_A ⟶ ω_B` of the dualizing complexes along a morphism `a`: the
exceptional adjoint of `ω_A ≅ Ra^! ω_B`. For proper `a` it is
`ProEtale.CondensedRing.lowerStarDualizingComplexTrace` read through `Ra_! ≅ Ra_*`. -/
noncomputable def lowerShriekDualizingComplexTrace (a : A ⟶ B) :
    (boundedConstructibleLowerShriek ℓ a).obj
        (dualizingComplex' ℓ A) ⟶ dualizingComplex' ℓ B :=
  (boundedConstructibleLowerShriek ℓ a).map
      (dualizingComplexComp ℓ a).inv ≫
    (boundedConstructibleUpperShriekAdjunction ℓ a).counit.app _

lemma lowerShriek_map_eqToHom_comp_counit {r r' : A ⟶ B} (h : r = r')
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ r).map
        (eqToHom (congrArg (fun s ↦
          (boundedConstructibleUpperShriek ℓ s).obj N) h.symm)) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ r).counit.app N =
    eqToHom (by subst h; rfl) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ r').counit.app
          N := by
  subst h
  simp

/-- The adjoint of the trace `t_a` along the structure morphism `a_B` of `B`:
`Ra_{B!} t_a ≫ ε = R(a ≫ a_B)_! ≅ Ra_{A!}` followed by the counit. -/
lemma lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit (a : A ⟶ B) :
    (boundedConstructibleLowerShriek ℓ (toPoint B)).map
        (lowerShriekDualizingComplexTrace ℓ a) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ (toPoint B)).counit.app (𝟙_ _) =
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a (toPoint B)).inv.app
        (dualizingComplex' ℓ A) ≫
      eqToHom (by rw [comp_toPoint]; rfl) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ (toPoint A)).counit.app (𝟙_ _) := by
  have hP := Adjunction.map_map_conjugateIsoEquiv_comp_counit
    (boundedConstructibleUpperShriekAdjunction ℓ a)
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint B))
    (boundedConstructibleUpperShriekAdjunction ℓ (a ≫ toPoint B))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a (toPoint B)) (𝟙_ _)
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a (toPoint B)).inv.naturality
    (eqToHom (congrArg (fun s ↦
      (boundedConstructibleUpperShriek ℓ s).obj (𝟙_ _))
        (comp_toPoint a).symm))
  have he := lowerShriek_map_eqToHom_comp_counit ℓ (comp_toPoint a) (𝟙_ _)
  simp only [Functor.comp_map] at hn
  simp only [lowerShriekDualizingComplexTrace, dualizingComplexComp,
    boundedConstructibleUpperShriekComp_padicAlgCl, Iso.trans_inv, Iso.symm_inv, Iso.app_hom,
    eqToIso.inv, Functor.map_comp, Category.assoc] at hP ⊢
  rw [hP, reassoc_of% hn, he]

@[reassoc]
lemma lowerShriek_map_comp_eqToHom {r r' : A ⟶ B} (h : r = r')
    {M N : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : M ⟶ N) :
    (boundedConstructibleLowerShriek ℓ r).map φ ≫
        eqToHom (congrArg (fun s ↦
          (boundedConstructibleLowerShriek ℓ s).obj N) h) =
      eqToHom (congrArg (fun s ↦
          (boundedConstructibleLowerShriek ℓ s).obj M) h) ≫
        (boundedConstructibleLowerShriek ℓ r').map φ := by
  subst h
  simp

@[reassoc]
lemma lowerShriekComp_hom_app_comp_eqToHom {r r' : B ⟶ C} (h : r = r') (a : A ⟶ B)
    (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a r).hom.app M ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a r').hom.app M := by
  subst h
  simp

/-- **The trace is compatible with composition**: `t_{a ≫ b} = t_b ∘ Rb_! t_a`, read through
`R(a ≫ b)_! ≅ Ra_! ⋙ Rb_!`. -/
theorem lowerShriekDualizingComplexTrace_comp (a : A ⟶ B) (b : B ⟶ C) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).hom.app (dualizingComplex' ℓ A) ≫
        (boundedConstructibleLowerShriek ℓ b).map
          (lowerShriekDualizingComplexTrace ℓ a) ≫ lowerShriekDualizingComplexTrace ℓ b =
      lowerShriekDualizingComplexTrace ℓ (a ≫ b) := by
  apply ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint C)).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have pa := lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit ℓ a
  have pb := lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit ℓ b
  have pab := lowerShriek_map_lowerShriekDualizingComplexTrace_comp_counit ℓ (a ≫ b)
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b (toPoint C)).inv.naturality
    (lowerShriekDualizingComplexTrace ℓ a)
  simp only [Functor.comp_map] at hn
  have he := lowerShriek_map_comp_eqToHom ℓ (comp_toPoint b) (lowerShriekDualizingComplexTrace ℓ a)
  have hc := lowerShriekComp_hom_app_comp_eqToHom ℓ (comp_toPoint b) a (dualizingComplex' ℓ A)
  have hassoc := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ a b (toPoint C)
    (dualizingComplex' ℓ A)
  have hassoc' : (boundedConstructibleLowerShriek ℓ
      (toPoint C)).map ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).hom.app
        (dualizingComplex' ℓ A)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b (toPoint C)).inv.app
        ((boundedConstructibleLowerShriek ℓ a).obj
          (dualizingComplex' ℓ A)) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (a ≫ b) (toPoint C)).inv.app
          (dualizingComplex' ℓ A) ≫ eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a (b ≫ toPoint C)).hom.app
          (dualizingComplex' ℓ A) := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (a ≫ b)
      (toPoint C)).hom.app (dualizingComplex' ℓ A)), reassoc_of% hassoc]
    simp
  rw [pb, reassoc_of% hn, reassoc_of% he, pa, pab, reassoc_of% hassoc', reassoc_of% hc,
      Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc,
    eqToHom_trans_assoc]

section Coherence

variable {D : Over (Spec (.of k))} [LocallyOfFiniteType D.hom] [QuasiCompact D.hom]
  [IsSeparated D.hom]


@[reassoc]
lemma lowerShriekComp_hom_app_map_inv_app (x : A ⟶ B) (y : B ⟶ C) (z : C ⟶ D)
    (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ y z).hom.app
        ((boundedConstructibleLowerShriek ℓ x).obj M) ≫
            (boundedConstructibleLowerShriek ℓ z).map
                ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x (y ≫ z)).inv.app M ≫
          eqToHom (by rw [Category.assoc]) ≫ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (x ≫
              y) z).hom.app M := by
  have h := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ x y z M
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x (y ≫ z)).hom.app M),
    ← cancel_epi (eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek
        ℓ r).obj M) (Category.assoc x y z)))]
  rw [← reassoc_of% h]
  simp [← Functor.map_comp]

@[reassoc]
lemma lowerShriekComp_hom_app_comp_hom_app (x : A ⟶ B) (y : B ⟶ C) (z : C ⟶ D)
    (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x (y ≫ z)).hom.app M ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ y z).hom.app
            ((boundedConstructibleLowerShriek ℓ x).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (x ≫
          y) z).hom.app M ≫
        (boundedConstructibleLowerShriek ℓ z).map
            ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app M) := by
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_assoc]
  simp

@[reassoc]
lemma lowerShriek_map_lowerShriekComp_hom_app_comp_inv_app (x : A ⟶ B) (y : B ⟶ C)
    (z : C ⟶ D) (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ z).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app M) ≫
            (boundedConstructibleLowerShriekComp_padicAlgCl ℓ y z).inv.app
                ((boundedConstructibleLowerShriek ℓ x).obj M) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (x ≫ y) z).inv.app M ≫
          eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x (y ≫ z)).hom.app M := by
  have h := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ x y z M
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (x ≫
      y) z).hom.app M), reassoc_of% h]
  simp

@[reassoc]
lemma lowerShriek_map_lowerShriekComp_inv_app_comp_inv_app (x : A ⟶ B) (y : B ⟶ C)
    (z : C ⟶ D) (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ z).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M) ≫
            (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (x ≫ y) z).inv.app M =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ y z).inv.app
          ((boundedConstructibleLowerShriek ℓ x).obj M) ≫
              (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x (y ≫ z)).inv.app M ≫
        eqToHom (by rw [Category.assoc]) := by
  have h := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ x y z M
  rw [← cancel_epi ((boundedConstructibleLowerShriek ℓ z).map
      ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).hom.app M)),
    ← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (x ≫ y) z).hom.app M),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app, reassoc_of% h]
  simp

@[reassoc]
lemma lowerShriek_map_lowerShriekComp_inv_app_comp_eqToHom_comp_inv_app (x : A ⟶ B) (y : B ⟶ C)
    (z : C ⟶ D) {u : A ⟶ C} (hu : x ≫ y = u) (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ z).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ x y).inv.app M) ≫
      (boundedConstructibleLowerShriek ℓ z).map
        (eqToHom (by rw [hu])) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u z).inv.app M =
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ y z).inv.app
        ((boundedConstructibleLowerShriek ℓ x).obj M) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ x (y ≫ z)).inv.app M ≫
      eqToHom (by rw [← hu, Category.assoc]) := by
  subst hu
  simp [lowerShriek_map_lowerShriekComp_inv_app_comp_inv_app]

@[reassoc]
lemma lowerShriekComp_hom_app_comp_map_eqToHom {u u' : A ⟶ B} (h : u = u') (z : B ⟶ C)
    (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u z).hom.app M ≫
        (boundedConstructibleLowerShriek ℓ z).map (eqToHom
            (congrArg (fun s ↦ (boundedConstructibleLowerShriek ℓ
                s).obj M) h)) =
      eqToHom (by rw [h]) ≫ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u' z).hom.app M := by
  subst h
  simp

@[reassoc]
lemma lowerShriek_map_eqToHom_comp_lowerShriekComp_inv_app {u u' : A ⟶ B} (h : u = u')
    (z : B ⟶ C) (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ z).map (eqToHom (congrArg
        (fun s ↦ (boundedConstructibleLowerShriek ℓ s).obj M) h)) ≫
            (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u' z).inv.app M =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u z).inv.app M ≫ eqToHom (by rw [h]) := by
  subst h
  simp

@[reassoc]
lemma eqToHom_comp_lowerShriekComp_inv_app {r r' : B ⟶ C} (h : r = r') (a : A ⟶ B)
    (M : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    eqToHom (by rw [h]) ≫ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a r').inv.app M =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a r).inv.app M ≫ eqToHom (congrArg (fun s ↦
        (boundedConstructibleLowerShriek ℓ (a ≫ s)).obj M) h) := by
  subst h
  simp

lemma eqToHom_comp_lowerShriekDualizingComplexTrace {r r' : A ⟶ B} (h : r = r') :
    eqToHom (congrArg (fun s ↦ (boundedConstructibleLowerShriek ℓ
        s).obj (dualizingComplex' ℓ A)) h) ≫
        lowerShriekDualizingComplexTrace ℓ r' = lowerShriekDualizingComplexTrace ℓ r := by
  subst h
  simp

end Coherence

section Exchange

variable {Fc Cc Xc Pc Fb Cb Yb Pb : Over (Spec (.of k))}
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

/-- **Exchange of the traces of two squares along a map of squares**, on compactly supported
direct images: for squares `ιc ≫ c = dc ≫ Δc` and `ιb ≫ b = db ≫ Δb` and a map
`(h, g, f, q)` between them, the two maps `Rb_! Rg_! Rιc_! ω ⟶ RΔb_! ω` built from the
composition laws and the traces `t_dc`, `t_f`, resp. `t_h`, `t_db` agree. -/
@[reassoc]
theorem lowerShriekSquareIso_trace_exchange (wc : ιc ≫ c = dc ≫ Δc) (wb : ιb ≫ b = db ≫ Δb)
    (wgb : g ≫ b = c ≫ q) (wq : Δc ≫ q = f ≫ Δb) (wh : ιc ≫ g = h ≫ ιb)
    (whd : dc ≫ f = h ≫ db) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app
        ((boundedConstructibleLowerShriek ℓ ιc).obj
          (dualizingComplex' ℓ Fc)) ≫
      eqToHom (by rw [wgb]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app
        ((boundedConstructibleLowerShriek ℓ ιc).obj
          (dualizingComplex' ℓ Fc)) ≫
      (boundedConstructibleLowerShriek ℓ q).map
        ((boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wc).hom.app
          (dualizingComplex' ℓ Fc)) ≫
      (boundedConstructibleLowerShriek ℓ q).map
        ((boundedConstructibleLowerShriek ℓ Δc).map
          (lowerShriekDualizingComplexTrace ℓ dc)) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ Δc q).inv.app (dualizingComplex' ℓ Xc) ≫
      eqToHom (by rw [wq]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f Δb).hom.app (dualizingComplex' ℓ Xc) ≫
      (boundedConstructibleLowerShriek ℓ Δb).map
        (lowerShriekDualizingComplexTrace ℓ f) =
    (boundedConstructibleLowerShriek ℓ b).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ ιc g).inv.app (dualizingComplex' ℓ Fc) ≫
          eqToHom (by rw [wh]) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h ιb).hom.app (dualizingComplex' ℓ Fc) ≫
          (boundedConstructibleLowerShriek ℓ ιb).map
            (lowerShriekDualizingComplexTrace ℓ h)) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wb).hom.app (dualizingComplex' ℓ Fb) ≫
      (boundedConstructibleLowerShriek ℓ Δb).map
        (lowerShriekDualizingComplexTrace ℓ db) := by
  have T₁ : (boundedConstructibleLowerShriek ℓ f).map
      (lowerShriekDualizingComplexTrace ℓ dc) ≫ lowerShriekDualizingComplexTrace ℓ f =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ dc f).inv.app (dualizingComplex' ℓ Fc) ≫
        eqToHom (by rw [whd]) ≫ lowerShriekDualizingComplexTrace ℓ (h ≫ db) := by
    rw [eqToHom_comp_lowerShriekDualizingComplexTrace ℓ whd, ←
        lowerShriekDualizingComplexTrace_comp,
      Iso.inv_hom_id_app_assoc]
  have T₂ : (boundedConstructibleLowerShriek ℓ db).map
      (lowerShriekDualizingComplexTrace ℓ h) ≫ lowerShriekDualizingComplexTrace ℓ db =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h db).inv.app (dualizingComplex' ℓ Fc) ≫
        lowerShriekDualizingComplexTrace ℓ (h ≫ db) := by
    rw [← lowerShriekDualizingComplexTrace_comp, Iso.inv_hom_id_app_assoc]
  have n₁ := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ Δc q).inv.naturality
    (lowerShriekDualizingComplexTrace ℓ dc)
  have n₂ := lowerShriek_map_comp_eqToHom ℓ wq (lowerShriekDualizingComplexTrace ℓ dc)
  have n₃ := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f Δb).hom.naturality
    (lowerShriekDualizingComplexTrace ℓ dc)
  have n₄ := (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ wb).hom.naturality
    (lowerShriekDualizingComplexTrace ℓ h)
  simp only [Functor.comp_map] at n₁ n₃ n₄
  simp only [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% n₃]
  simp only [← (boundedConstructibleLowerShriek ℓ Δb).map_comp
    ((boundedConstructibleLowerShriek ℓ f).map (lowerShriekDualizingComplexTrace ℓ dc))
    (lowerShriekDualizingComplexTrace ℓ f), T₁]
  simp only [Functor.map_comp, Category.assoc]
  simp only [reassoc_of% n₄]
  simp only [← (boundedConstructibleLowerShriek ℓ Δb).map_comp
    ((boundedConstructibleLowerShriek ℓ db).map (lowerShriekDualizingComplexTrace ℓ h))
    (lowerShriekDualizingComplexTrace ℓ db), T₂]
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, NatTrans.comp_app, eqToHom_app, Functor.map_comp, Category.assoc]
  simp only [lowerShriekComp_hom_app_map_inv_app_assoc,
    lowerShriekComp_hom_app_comp_map_eqToHom_assoc ℓ wc,
    Iso.hom_inv_id_app_assoc, lowerShriekComp_hom_app_comp_eqToHom_assoc ℓ wq,
    lowerShriekComp_hom_app_comp_map_eqToHom_assoc ℓ whd,
    eqToHom_comp_lowerShriekComp_inv_app_assoc ℓ wgb,
    lowerShriek_map_lowerShriekComp_hom_app_comp_inv_app_assoc,
    lowerShriekComp_hom_app_comp_eqToHom_assoc ℓ wb]
  rw [lowerShriek_map_lowerShriekComp_inv_app_comp_eqToHom_comp_inv_app_assoc ℓ ιc g b wh]
  simp only [eqToHom_trans_assoc]

end Exchange

section LowerStar

variable {D : Over (Spec (.of k))} [LocallyOfFiniteType D.hom] [QuasiCompact D.hom]
  [IsSeparated D.hom]

lemma lowerStarComp_inv_app_eq (a : A ⟶ B) (b : B ⟶ C) [IsProper a.left] [IsProper b.left]
    [IsProper (a ≫ b).left] (K : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStarComp ℓ a b).inv.app K =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (a ≫ b)).inv.app K ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).hom.app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ b).hom.app
          ((boundedConstructibleLowerShriek ℓ a).obj K) ≫
        (boundedConstructibleLowerStar ℓ b).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).hom.app K) := by
  rw [boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp, Iso.inv_hom_id_app_assoc]

lemma lowerStarComp_hom_app_eq (a : A ⟶ B) (b : B ⟶ C) [IsProper a.left] [IsProper b.left]
    [IsProper (a ≫ b).left] (K : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStarComp ℓ a b).hom.app K =
      (boundedConstructibleLowerStar ℓ b).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).inv.app K) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ b).inv.app
          ((boundedConstructibleLowerShriek ℓ a).obj K) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).inv.app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (a ≫ b)).hom.app K := by
  rw [← cancel_mono ((boundedConstructibleLowerStarComp ℓ a
    b).inv.app K), Iso.hom_inv_id_app, lowerStarComp_inv_app_eq]
  simp [← Functor.map_comp]

@[reassoc]
lemma lowerShriekIsoLowerStar_hom_app_comp_eqToHom {r r' : A ⟶ B} (h : r = r') [IsProper r.left]
    [IsProper r'.left] (K : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).hom.app K ≫
        eqToHom (congrArg (fun s ↦
          (boundedConstructibleLowerStar ℓ s).obj K) h) =
      eqToHom (congrArg (fun s ↦
          (boundedConstructibleLowerShriek ℓ s).obj K) h) ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r').hom.app K := by
  subst h
  simp

end LowerStar

end AlgebraicGeometry.ProEtale.CondensedRing
