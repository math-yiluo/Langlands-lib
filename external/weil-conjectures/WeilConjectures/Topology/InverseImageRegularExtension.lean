/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
import Mathlib.CategoryTheory.Limits.Final.Type
import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-! # Extension of the inverse image of a regular module

Source: Stacks Project, Sheaves on Spaces, Tags 008X, 008Y and 008A.
(blueprint: stage3-inverse-image-regular-extension).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings
namespace SheafOfModules
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option hygiene false in
local notation "𝓡" S =>
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S

private def isoOfHomEquiv {C : Type*} [Category C] (M N : C)
    (e : ∀ P, (M ⟶ P) ≃ (N ⟶ P))
    (he : ∀ P Q (a : M ⟶ P) (b : P ⟶ Q), e Q (a ≫ b) = e P a ≫ b) : M ≅ N where
  hom := (e N).symm (𝟙 N)
  inv := e M (𝟙 M)
  hom_inv_id := by
    apply (e M).injective
    rw [he, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := he M N (𝟙 M) ((e N).symm (𝟙 N))
    simpa using h.symm

/-- A natural hom equivalence and a natural equivalence on sections identify a representing
module with the regular module. Keeping the functor abstract avoids unfolding scalar restrictions
in the naturality and normalization calculations. -/
private theorem exists_unitIso_of_sections
    {T T' : TopCat.{u}} {R : T'.Sheaf RingCat.{u}} {S : T.Sheaf RingCat.{u}}
    (H : SheafOfModules.{u} S ⥤ SheafOfModules.{u} R) (F : SheafOfModules.{u} S)
    (q : ∀ N, (F ⟶ N) ≃ (unit R ⟶ H.obj N))
    (hq : ∀ N N' (a : F ⟶ N) (b : N ⟶ N'), q N' (a ≫ b) = q N a ≫ H.map b)
    (se : ∀ N, N.sections ≃ (H.obj N).sections)
    (hse : ∀ N N' (b : N ⟶ N') (s : N.sections),
      se N' (sectionsMap b s) = sectionsMap (H.map b) (se N s)) :
    ∃ e : F ≅ unit S,
      (H.obj (unit S)).unitHomEquiv (q (unit S) e.hom) =
        se (unit S) ((unit S).unitHomEquiv (𝟙 (unit S))) := by
  let eqv (N : SheafOfModules.{u} S) : (F ⟶ N) ≃ (unit S ⟶ N) :=
    (q N).trans ((H.obj N).unitHomEquiv.trans ((se N).symm.trans N.unitHomEquiv.symm))
  have heqv (N : SheafOfModules.{u} S) (a : F ⟶ N) :
      se N (N.unitHomEquiv (eqv N a)) = (H.obj N).unitHomEquiv (q N a) := by
    exact (congrArg (se N) (N.unitHomEquiv.apply_symm_apply
      ((se N).symm ((H.obj N).unitHomEquiv (q N a))))).trans
        ((se N).apply_symm_apply _)
  have hn (N N' : SheafOfModules.{u} S) (a : F ⟶ N) (b : N ⟶ N') :
      eqv N' (a ≫ b) = eqv N a ≫ b := by
    apply N'.unitHomEquiv.injective
    apply (se N').injective
    rw [heqv, unitHomEquiv_comp_apply, hq, unitHomEquiv_comp_apply, hse, heqv]
  let e := isoOfHomEquiv F (unit S) eqv hn
  refine ⟨e, ?_⟩
  exact (heqv (unit S) e.hom).symm.trans
    (congrArg (fun z ↦ se (unit S) ((unit S).unitHomEquiv z))
      ((eqv (unit S)).apply_symm_apply (𝟙 (unit S))))

/-- Compose an adjunction with a natural hom equivalence before identifying the regular module. -/
private theorem exists_unitIso_of_adjunction_sections
    {T T' : TopCat.{u}} {R : T'.Sheaf RingCat.{u}} {S : T.Sheaf RingCat.{u}}
    {D : Type*} [Category.{u} D]
    (Q : D ⥤ SheafOfModules.{u} R) (L : SheafOfModules.{u} S ⥤ D)
    (E : D ⥤ SheafOfModules.{u} S) (adj : E ⊣ L) (I : D)
    (φ : ∀ N, (I ⟶ N) ≃ (unit R ⟶ Q.obj N))
    (hnφ : ∀ N N' (a : I ⟶ N) (b : N ⟶ N'), φ N' (a ≫ b) = φ N a ≫ Q.map b)
    (se : ∀ N, N.sections ≃ (Q.obj (L.obj N)).sections)
    (hse : ∀ N N' (b : N ⟶ N') (s : N.sections),
      se N' (sectionsMap b s) = sectionsMap (Q.map (L.map b)) (se N s)) :
    ∃ e : E.obj I ≅ unit S,
      (Q.obj (L.obj (unit S))).unitHomEquiv
        (φ (L.obj (unit S)) (adj.homEquiv I (unit S) e.hom)) =
          se (unit S) ((unit S).unitHomEquiv (𝟙 (unit S))) := by
  let q (N : SheafOfModules.{u} S) : (E.obj I ⟶ N) ≃ (unit R ⟶ Q.obj (L.obj N)) :=
    (adj.homEquiv I N).trans (φ (L.obj N))
  have hnq (N N' : SheafOfModules.{u} S) (a : E.obj I ⟶ N) (b : N ⟶ N') :
      q N' (a ≫ b) = q N a ≫ Q.map (L.map b) := by
    dsimp only [q, Equiv.trans_apply]
    rw [adj.homEquiv_naturality_right, hnφ]
  exact exists_unitIso_of_sections (L ⋙ Q) (E.obj I) q hnq se hse

/-- Extending the inverse image of the regular module gives the regular target module,
with the canonical unit normalization.
Source: Stacks Project, Sheaves on Spaces, Tags 008X, 008Y and 008A.
(blueprint: stage3-inverse-image-regular-extension).

Proof: Compose the change-of-rings hom equivalence with the inverse-image
module hom equivalence. Maps from the regular source module correspond to
compatible global sections. Precomposition by the inverse-image map on opens
is a bijection on compatible sections, since that functor is final. Thus maps
from the extended inverse-image regular module to any B-module correspond,
naturally in that module, to maps from the regular B-module. The elementary
representable-functor argument constructs inverse module maps. For their unit
normalization, the two adjunction section formulas identify the adjunct of
the forward isomorphism on a with its value on the sheafification of 1 tensor
the abelian inverse-image unit of a. The hom equivalence sends that isomorphism
to the identity of the regular B-module, so its adjunct sends 1 to 1.
Linearity then sends a = a • 1 to t(η_A(a)) • 1 = t(η_A(a)). This applies also
to zero rings and empty opens, since neither the section equivalence nor the
identity and linearity calculations use nontriviality or nonemptiness. -/
theorem inverseImageRegularExtension
    {T T' : TopCat.{u}} (g : T ⟶ T') (A : T'.Sheaf CommRingCat.{u})
    (B : T.Sheaf CommRingCat.{u}) (t : TopCat.Sheaf.inverseImageRing g A ⟶ B) :
    ∃ e : changeOfRings.{u, u, u} t
        (TopCat.Sheaf.inverseImageModule g A (unit (𝓡 A))) ≅ unit (𝓡 B),
      ∀ (V : (Opens T')ᵒᵖ) (a : A.obj.obj V),
        e.hom.val.app ((Opens.map g).op.obj V)
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
            (changeOfRingsPresheaf.{u, u, u} t
              (TopCat.Sheaf.inverseImageModule g A (unit (𝓡 A))))).app
                ((Opens.map g).op.obj V)
                ((1 : B.obj.obj ((Opens.map g).op.obj V)) ⊗ₜ[
                  (TopCat.Sheaf.inverseImageRing g A).obj.obj ((Opens.map g).op.obj V),
                  (t.hom.app ((Opens.map g).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map g) AddCommGrpCat.{u} (Opens.grothendieckTopology T')
                    (Opens.grothendieckTopology T)).unit.app
                      ((toSheaf (𝓡 A)).obj (unit (𝓡 A)))).hom.app V a))) =
          (t.hom.app ((Opens.map g).op.obj V)).hom
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map g) CommRingCat.{u} (Opens.grothendieckTopology T')
              (Opens.grothendieckTopology T)).unit.app A).hom.app V a) := by
  classical
  let R := 𝓡 A
  let S := 𝓡 B
  let C := TopCat.Sheaf.inverseImageRing g A
  let η : R ⟶ ((Opens.map g).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology T') (Opens.grothendieckTopology T)).obj (𝓡 C) :=
    (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map g) CommRingCat.{u} (Opens.grothendieckTopology T')
        (Opens.grothendieckTopology T)).unit.app A)
  let Q := pushforward.{u} (F := Opens.map g) η
  let L := restrictScalars ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map t)
  let M := unit R
  let I := TopCat.Sheaf.inverseImageModule g A M
  let F := changeOfRings.{u, u, u} t I
  obtain ⟨E, hE, adj, hadj⟩ := exists_changeOfRingsAdjunction T C B t
  obtain ⟨φ, hφ, _, hnφ⟩ := moduleInverseImageAdjunction g A
  let se (N : SheafOfModules.{u} S) : N.sections ≃ (Q.obj (L.obj N)).sections :=
    Equiv.ofBijective ((Opens.map g).op.sectionsPrecomp)
      (Functor.bijective_sectionsPrecomp (Opens.map g).op
        (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}))
  obtain ⟨e₀, hs⟩ := exists_unitIso_of_adjunction_sections Q L E adj I (φ M) (hnφ M)
    se (fun _ _ _ _ ↦ rfl)
  let e : F ≅ unit S := (eqToIso (hE I)).symm ≪≫ e₀
  have he : eqToHom (hE I) ≫ e.hom = e₀.hom := by
    simp [e]
  let p : M ⟶ Q.obj (L.obj (unit S)) :=
    φ M (L.obj (unit S)) (adj.homEquiv I (unit S) e₀.hom)
  refine ⟨e, ?_⟩
  intro V a
  have hv := congrArg (fun z ↦ z.val V) hs
  change p.val.app V (1 : A.obj.obj V) =
    (1 : B.obj.obj ((Opens.map g).op.obj V)) at hv
  trans p.val.app V a
  · have hadj' := hadj I (unit S) e.hom ((Opens.map g).op.obj V)
    rw [he] at hadj'
    exact ((hφ M (L.obj (unit S)) (adj.homEquiv I (unit S) e₀.hom) V a).trans
      (hadj' _)).symm
  have ha := (p.val.app V).hom.map_smul a (1 : A.obj.obj V)
  rw [show a • (1 : A.obj.obj V) = a from mul_one a, hv] at ha
  exact ha.trans (@mul_one (B.obj.obj ((Opens.map g).op.obj V)) _ _)


end
end SheafOfModules
