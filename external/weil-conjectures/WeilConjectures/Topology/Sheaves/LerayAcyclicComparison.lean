/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.Topology.TopologicalLeraySpectralSequence

/-!
# Leray comparison for an acyclic abelian sheaf

Source: Stacks Project, Cohomology of Sheaves, Tags 01F2 and 01F4 (1)
(blueprint: lem-sc-leray-closed-pushforward-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

-- Evaluation preserves the kernel and cokernel descriptions of cycles and homology.
private lemma mapped_iCycles_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (i : ι)
    (h : G.map (K.d i (c.next i)) = 0) : IsIso (G.map (K.iCycles i)) := by
  exact KernelFork.IsLimit.isIso_ι _
    (isLimitForkMapOfIsLimit' G _ (K.cyclesIsKernel i (c.next i) rfl)) h

private lemma mapped_homologyπ_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (i : ι) (h : G.map (K.d (c.prev i) i) = 0) :
    IsIso (G.map (K.homologyπ i)) := by
  have hz : G.map (K.toCycles (c.prev i) i) = 0 := by
    apply (cancel_mono (G.map (K.iCycles i))).1
    simp only [zero_comp, ← G.map_comp, HomologicalComplex.toCycles_i, h]
  exact CokernelCofork.IsColimit.isIso_π _
    (isColimitCoforkMapOfIsColimit' G _ (K.homologyIsCokernel (c.prev i) i rfl)) hz

private lemma mapped_homology_isZero
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (i : ι) (h : IsZero (G.obj (K.X i))) : IsZero (G.obj (K.homology i)) := by
  exact IsZero.of_epi (G.map (K.homologyπ i))
    (IsZero.of_mono (G.map (K.iCycles i)) h)

-- A zero term remains zero on every subsequent page.
private lemma mapped_page_isZero
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (E : E₂CohomologicalSpectralSequenceNat C)
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : ∀ a q : ℕ, 0 < q → IsZero (G.obj ((E.page 2).X (a, q))))
    (r : ℤ) (hr : 2 ≤ r) (a q : ℕ) (hq : 0 < q) :
    IsZero (G.obj ((E.page r hr).X (a, q))) := by
  induction r, hr using Int.leInduction with
  | base => exact h a q hq
  | succ r hr ih =>
    exact (mapped_homology_isZero (E.page r hr) G (a, q) ih).of_iso
      (G.mapIso (E.iso r (r + 1) (a, q) (hr := hr))).symm

-- On row zero, the outgoing differential is outside the first quadrant and the incoming
-- differential has zero source after evaluation.
private lemma mapped_bottom_transition_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (E : E₂CohomologicalSpectralSequenceNat C)
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : ∀ a q : ℕ, 0 < q → IsZero (G.obj ((E.page 2).X (a, q))))
    (p : ℕ) (r : ℤ) (hr : 2 ≤ r)
    (t : (E.page r hr).X (p, 0) ⟶ (E.page (r + 1)).X (p, 0))
    (ht : (E.page r hr).iCycles (p, 0) ≫ t =
      (E.page r hr).homologyπ (p, 0) ≫ (E.iso r (r + 1) (p, 0) (hr := hr)).hom) :
    IsIso (G.map t) := by
  let c := ComplexShape.spectralSequenceNat (r, 1 - r)
  have hout : G.map ((E.page r hr).d (p, 0) (c.next (p, 0))) = 0 := by
    rw [(E.page r hr).shape _ _ (by simp [c]; omega), G.map_zero]
  have hin : G.map ((E.page r hr).d (c.prev (p, 0)) (p, 0)) = 0 := by
    by_cases hrel : c.Rel (c.prev (p, 0)) (p, 0)
    · have hq : 0 < (c.prev (p, 0)).2 := by
        have hh : ((c.prev (p, 0)).2 : ℤ) + (1 - r) = 0 := hrel.2
        omega
      exact (mapped_page_isZero E G h r hr _ _ hq).eq_of_src _ _
    · rw [(E.page r hr).shape _ _ hrel, G.map_zero]
  have := mapped_iCycles_isIso (E.page r hr) G (p, 0) hout
  have := mapped_homologyπ_isIso (E.page r hr) G (p, 0) hin
  have heq : G.map t = inv (G.map ((E.page r hr).iCycles (p, 0))) ≫
      G.map ((E.page r hr).homologyπ (p, 0)) ≫
      G.map (E.iso r (r + 1) (p, 0) (hr := hr)).hom := by
    rw [← G.map_comp, ← ht, G.map_comp, IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

-- Vanishing graded pieces make each inclusion an isomorphism, starting from F⁰ = H.
private lemma mapped_filtration_arrow_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {A : C} (T : DecreasingFiltration A)
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (p : ℕ) (htop : T.step 0 = ⊤)
    (hzero : ∀ a : ℕ, a < p → IsZero (G.obj (T.gradedPiece a))) :
    IsIso (G.map (T.step p).arrow) := by
  have h (a : ℕ) (ha : a ≤ p) : IsIso (G.map (T.step a).arrow) := by
    induction a with
    | zero => rw [Nat.cast_zero, htop]; infer_instance
    | succ a ih =>
      have := ih (by omega)
      let j := Subobject.ofLE (T.step (a + 1)) (T.step a)
        (T.antitone_step (by omega))
      have : Epi (G.map j) := Preadditive.epi_of_isZero_cokernel' _
        (isColimitCoforkMapOfIsColimit' G (cokernel.condition j) (cokernelIsCokernel j))
        (hzero a (by omega))
      have := isIso_of_mono_of_epi (G.map j)
      have heq : G.map (T.step (a + 1)).arrow = G.map j ≫ G.map (T.step a).arrow := by
        rw [← G.map_comp, Subobject.ofLE_arrow]
      simpa only [Nat.cast_add, Nat.cast_one] using heq ▸
        (inferInstance : IsIso (G.map j ≫ G.map (T.step a).arrow))
  exact h p le_rfl

/-- The natural Leray edge is an isomorphism on sheaves with vanishing higher direct images.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F2 and 01F4 (1)
(blueprint: lem-sc-leray-closed-pushforward-cohomology).

Here `a` is the canonical map from the free abelian sheaf on the terminal open of `X`
to the direct image of that on `Z`: its value on every free generator is the corresponding
free generator on the inverse-image open. The cocycle equation characterizes the edge:
lift an injective resolution of the direct image to the direct image of an injective
resolution, and use the same global cocycle on `Z`. Quantifying over all such lifts makes
this characterization independent of the resolutions and comparison maps.

Proof:
1. Apply lem-sc-topological-leray-spectral-sequence to obtain the first-quadrant Leray
spectral sequence with E₂^{a,b} = H^a(X,R^b f_*F), its finite abutment filtration and the
natural bottom edge H^p(X,f_*F) → H^p(Z,F). The injective-resolution construction of this
edge gives the displayed cocycle characterization and naturality.
2. If all positive higher direct images vanish, only row zero remains. Every differential
on each page r ≥ 2 has source or target outside that row, and hence vanishes. Thus E∞ = E₂.
For total degree p all graded pieces except the p-th vanish. The finite filtration therefore
identifies its p-th piece with the whole abutment H^p(Z,F). Consequently the same edge map
is an isomorphism, whose inverse gives the comparison in the direction stated in the node. -/
theorem exists_lerayEdge_isIso_of_acyclic {Z X : TopCat.{u}} (f : Z ⟶ X) :
    ∃ a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)),
      (∀ (U : Opens X) (g : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
            ((toSheafify (Opens.grothendieckTopology X)
              (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app (op U)
                (FreeAbelianGroup.of g)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
                (FreeAbelianGroup.of
                  ((Opens.map f).map g ≫ eqToHom (Opens.map_top f)))) ∧
      ∃ ε : ∀ p : ℕ,
        pushforwardAb f ⋙ Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) ⟶
          Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) p ⋙
            (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤),
        (∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
          (I : InjectiveResolution F) (J : InjectiveResolution ((pushforwardAb f).obj F))
          (φ : J.cocomplex ⟶ ((pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)
          (_hφ : J.ι.f 0 ≫ φ.f 0 = (pushforwardAb f).map (I.ι.f 0))
          (p : ℕ)
          (s : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ J.cocomplex.X p)
          (hs : s ≫ J.cocomplex.d p (p + 1) = 0)
          (t : (presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X p)
          (ht : t ≫ I.cocomplex.d p (p + 1) = 0)
          (_hst : a ≫ (pushforwardAb f).map t = s ≫ φ.f p),
          (ε p).app F (J.extMk s (p + 1) rfl hs) = I.extMk t (p + 1) rfl ht) ∧
        (∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}),
          (∀ q : ℕ, 0 < q → IsZero
            ((@Functor.rightDerived _ _ _ _ _ _ _ (pushforwardAb f)
              (@Functor.additive_of_comp_faithful _ _ _ _ _ _ _ _ _ (pushforwardAb f)
                (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
                inferInstance
                (Functor.additive_of_iso
                  (F := sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⋙
                    (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj
                      (Opens.map f).op) (Iso.refl _)) inferInstance) q).obj F)) →
            ∀ p : ℕ, IsIso ((ε p).app F)) := by
  obtain ⟨HX, HZ, hX, hZ, E, e₂, _hstable, T, htop, _hbot, g, e₀, _he₀,
    t, ht, b, hb₂, hb, k, _hk, edge, hedge, a, ha, hcocycle⟩ :=
    exists_topological_leray_spectralSequence f
  have hXe : HX = fun p ↦ Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) p ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) := funext hX
  have hZe : HZ = fun p ↦ Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology Z) p ⋙
        (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) := funext hZ
  subst HX HZ
  refine ⟨a, ha, edge, ?_, ?_⟩
  · simpa using hcocycle
  · intro F hF p
    let G := (evaluation
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
      AddCommGrpCat.{u}).obj F
    have hzero (a q : ℕ) (hq : 0 < q) : IsZero (G.obj ((E.page 2).X (a, q))) := by
      exact (Functor.map_isZero
        (extFunctorObj
          ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)) a)
        (hF q hq)).of_iso (G.mapIso (e₂ a q))
    have hti (a : ℕ) (r : ℤ) (hr : 2 ≤ r) : IsIso (G.map (t a r hr)) :=
      mapped_bottom_transition_isIso E G hzero a r hr (t a r hr) (ht a r hr)
    have hbi (a : ℕ) (r : ℤ) (hr : 2 ≤ r) : IsIso (G.map (b a r hr)) := by
      induction r, hr using Int.leInduction with
      | base => rw [hb₂, G.map_id]; infer_instance
      | succ r hr ih => rw [hb a r hr, G.map_comp]; have := hti a r hr; infer_instance
    have hbi' := hbi p (p + 2) (by omega)
    have hgraded (a : ℕ) (ha : a < p) :
        IsZero (G.obj ((T p).gradedPiece a)) := by
      have hp : a + (p - a) = p := by omega
      have hz := mapped_page_isZero E G hzero
        ((a + (p - a) + 2 : ℕ) : ℤ) (by omega) a (p - a) (by omega)
      have hz' : IsZero (G.obj (E.pageInfinity (a, p - a))) := hz
      have hg := hz'.of_iso (G.mapIso (g a (p - a)))
      rw [hp] at hg
      exact hg
    have hinc := mapped_filtration_arrow_isIso (T p) G p (htop p) hgraded
    change IsIso (G.map (edge p))
    rw [hedge, G.map_comp, G.map_comp, G.map_comp]
    infer_instance

end TopCat.Sheaf
