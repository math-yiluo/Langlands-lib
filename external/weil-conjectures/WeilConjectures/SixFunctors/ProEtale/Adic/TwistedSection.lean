/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.WeilSheaf.ArtinSchreierInertia
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.StalkConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse

/-!
# A sheaf trivialised with a twisted deck action does not embed into a constant sheaf

Let `N` be an `ℓ`-adic sheaf on `Y`, and `w : Y' ⟶ Y` a morphism with an automorphism `g` over
`Y` (`g ≫ w = w`), such that `w^* N` is trivialised, `θ : ℚ̄_ℓ ≅ w^* N`, and `g` acts on the
trivialising section by a scalar `χ ≠ 1`. Let `z : S ⟶ Y` be a point which, after a base change
`π : Spec L ⟶ S` to a field, lifts along `w` to `z' : Spec L ⟶ Y'`, and suppose that `g`
restricts on `z'` to an automorphism `σ` of `Spec L` over `S`. Then `z^* N` does not embed into
a constant sheaf `ℚ̄_ℓⁿ` on `S`.

Indeed `σ` acts on the sections of `π^* z^* N` (the germs along `σ ≫ π = π`) and on those of
`π^* ℚ̄_ℓ`; a section of `π^* z^* N` coming from `θ` is multiplied by `χ`, while all sections of
`π^* ℚ̄_ℓ` are pulled back from `S` and so are fixed. Hence every morphism `z^* N ⟶ ℚ̄_ℓ`
kills that section after pullback, and a monomorphism into `ℚ̄_ℓⁿ` would kill it too.

This is the sheaf-theoretic content of "inertia acts on the fibre of `N` through the nontrivial
character `χ`", used for the Artin–Schreier sheaves at infinity (blueprint
`lemma-unramified-at-infinity-no-linear-characters--1`).

## Main statements

- `AlgebraicGeometry.ProEtale.factorGerm_eq_globalSectionsTransport`: germs are transports along
  squares with trivial base change.
- `AlgebraicGeometry.ProEtale.not_mono_upperStar_biproduct_unit_of_twist`: the main statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

section Coherence

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

lemma upperStarCongr_inv_app {P Y : Scheme.{u}} {a b : P ⟶ Y} (p : a = b)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A p).inv.app F = (upperStarCongr A p.symm).hom.app F := by
  subst p
  simp [upperStarCongr]

lemma upperStarCongr_hom_app_trans {P Y : Scheme.{u}} {a b c : P ⟶ Y} (p : a = b) (q : b = c)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A p).hom.app F ≫ (upperStarCongr A q).hom.app F =
      (upperStarCongr A (p.trans q)).hom.app F := by
  subst p q
  simp [upperStarCongr]

/-- `upperStarCongr` does not depend on the proof of the equality. The equality is taken between
the isomorphisms, not between their components, so the kernel compares the proofs instead of
unfolding the pullback functors. -/
lemma upperStarCongr_hom_app_eq_comp_id {P Y : Scheme.{u}} {a b : P ⟶ Y} (p q : a = b)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A p).hom.app F =
      (upperStarCongr A q).hom.app F ≫ 𝟙 ((b)^*[A].obj ((𝟭 _).obj F)) :=
  (@congrArg _ _ (upperStarCongr A p) (upperStarCongr A q) (fun e ↦ e.hom.app F) rfl).trans
    (Category.comp_id _).symm

/-- A germ is the transport along the square `y ≫ w = s ≫ 𝟙` with the trivial base change. -/
lemma factorGerm_eq_globalSectionsTransport {P W Y : Scheme.{u}} {w : W ⟶ Y} {y : P ⟶ W}
    {s : P ⟶ Y} (h : y ≫ w = s) (h' : y ≫ w = s ≫ 𝟙 Y) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    factorGerm A h F = globalSectionsTransport A h' ((upperStarId A Y).hom.app F) := by
  rw [factorGerm, globalSectionsTransport]
  congr 2
  rw [upperStarCompIso_hom_app, upperStarComp_id_right]
  simp only [upperStarFactor, Iso.trans_inv, NatTrans.comp_app, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.assoc, Category.id_comp]
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    upperStarCongr_inv_app]
  congr 1
  rw [← Category.assoc, upperStarCongr_hom_app_trans]
  exact upperStarCongr_hom_app_eq_comp_id A _ _ F

/-- Restricting a global section of `F` along `s` and then taking its germ along `y ≫ s = s` gives
the restriction along `s`. -/
lemma globalSectionsToUpperStar_app_comp_factorGerm {P Y : Scheme.{u}} {s : P ⟶ Y} {y : P ⟶ P}
    (h : y ≫ s = s) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (globalSectionsToUpperStar A s).app F ≫ factorGerm A h F =
      (globalSectionsToUpperStar A s).app F := by
  rw [factorGerm, ← Category.assoc, ← globalSectionsToUpperStar_comp, Category.assoc,
    ← Functor.map_comp]
  simp only [upperStarFactor, Iso.trans_inv, NatTrans.comp_app, Iso.hom_inv_id_app_assoc,
    upperStarCongr_inv_app]
  exact globalSectionsToUpperStar_app_comp_upperStarCongr (A := A) _ F

end Coherence

variable {l : ℕ} [Fact l.Prime]

/-- The global section of a composite `v ≫ g` is the image under `g` of the global section
of `v`. -/
lemma globalSectionOfModHom_comp {Z : Scheme.{u}} {M M' : AdicSheaf l Z}
    (v : AdicSheaf.unit l Z ⟶ M) (g : M ⟶ M') :
    globalSectionOfModHom (v ≫ g) = ((Sheaf.Γ _ _).map g.hom).hom (globalSectionOfModHom v) := by
  rw [globalSectionOfModHom_eq, globalSectionOfModHom_eq, Mod.comp_hom', Functor.map_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply]

lemma globalSectionOfModHom_zero {Z : Scheme.{u}} {M : AdicSheaf l Z} :
    globalSectionOfModHom (0 : AdicSheaf.unit l Z ⟶ M) = 0 := by
  rw [globalSectionOfModHom_eq]
  erw [Mod.zero_hom, Functor.map_zero]
  rfl

/-- The germ along an automorphism `σ` of `Spec L` over `S` fixes every section of the pullback
of `ℚ̄_ℓ` from `S`: these sections are multiples of the restriction of the section `1`. -/
lemma factorGerm_adicConstantSheaf_apply {S : Scheme.{u}} {L : Type u} [Field L]
    {π : Spec (.of L) ⟶ S} {σ : Spec (.of L) ⟶ Spec (.of L)} (hσ : σ ≫ π = π)
    (v : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of L))) (WeilCoefficients.{u} l)).obj
      ((π)^*[WeilCoefficients.{u} l].obj (adicConstantSheaf l S))) :
    (factorGerm (WeilCoefficients.{u} l) hσ (adicConstantSheaf l S)).hom v = v := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_globalSectionsToUpperStar_oneGlobalSection π v
  rw [map_smul]
  congr 1
  exact congrArg (fun φ ↦ φ.hom (oneGlobalSection (l := l) S))
    (globalSectionsToUpperStar_app_comp_factorGerm (WeilCoefficients.{u} l) hσ
      (adicConstantSheaf l S))

/-- The germ along `σ` of a section transported along `z' ≫ w = π ≫ z` is the transport of its
germ along `g`, when `σ ≫ z' = z' ≫ g`. -/
lemma globalSectionsTransport_comp_factorGerm {S Y Y' : Scheme.{u}} {L : Type u} [Field L]
    {π : Spec (.of L) ⟶ S} {σ : Spec (.of L) ⟶ Spec (.of L)} (hσ : σ ≫ π = π)
    {w : Y' ⟶ Y} {g : Y' ⟶ Y'} (hg : g ≫ w = w)
    {z : S ⟶ Y} {z' : Spec (.of L) ⟶ Y'} (hz : z' ≫ w = π ≫ z) (hσz : σ ≫ z' = z' ≫ g)
    (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    globalSectionsTransport _ hz (𝟙 ((z)^*[WeilCoefficients.{u} l].obj N)) ≫
        factorGerm (WeilCoefficients.{u} l) hσ ((z)^*[WeilCoefficients.{u} l].obj N) =
      factorGerm (WeilCoefficients.{u} l) hg N ≫ globalSectionsTransport _ hz (𝟙 _) := by
  let A := WeilCoefficients.{u} l
  have hσ' : σ ≫ π = π ≫ 𝟙 S := by rw [hσ, Category.comp_id]
  have hg' : g ≫ w = w ≫ 𝟙 Y := by rw [hg, Category.comp_id]
  rw [factorGerm_eq_globalSectionsTransport A hσ hσ',
    factorGerm_eq_globalSectionsTransport A hg hg']
  have h₁ : (σ ≫ z') ≫ w = π ≫ (𝟙 S ≫ z) := by
    rw [Category.assoc, hz, ← Category.assoc, hσ, Category.id_comp]
  have h₂ : (z' ≫ g) ≫ w = π ≫ (z ≫ 𝟙 Y) := by
    rw [Category.assoc, hg, hz, Category.comp_id]
  rw [globalSectionsTransport_comp A hz hσ' h₁, globalSectionsTransport_comp A hg' hz h₂,
    globalSectionsTransport_congr A h₁ (Category.id_comp z) _ (𝟙 _) ?_,
    globalSectionsTransport_congr A h₂ (Category.comp_id z) _ (𝟙 _) ?_,
    globalSectionsTransport_congr_left A _ hσz]
  · rw [upperStarComp_id_right]
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Category.assoc, Category.id_comp,
      Category.comp_id]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    simp only [Functor.id_obj, Category.id_comp]
    exact Category.comp_id _
  · rw [upperStarComp_id_left]
    simp only [Functor.comp_obj, Functor.id_obj, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Category.id_comp, NatTrans.naturality, Functor.id_map,
      Category.assoc, Iso.inv_hom_id_app_assoc, Category.comp_id]
    exact Category.comp_id _

/-- The global section of an isomorphism `ℚ̄_ℓ ≅ M` on a connected scheme is nonzero. -/
lemma globalSectionOfModHom_ne_zero_of_iso {Z : Scheme.{u}} [ConnectedSpace Z]
    {M : AdicSheaf l Z} (θ : AdicSheaf.unit l Z ≅ M) : globalSectionOfModHom θ.hom ≠ 0 := by
  intro h0
  have hφ : θ.hom = 0 :=
    (bijective_globalSectionOfModHom _).1 (h0.trans globalSectionOfModHom_zero.symm)
  have hone : 𝟙 (AdicSheaf.unit l Z) = 0 := by
    rw [← θ.hom_inv_id, hφ, zero_comp]
  refine oneGlobalSection_ne_zero (l := l) Z ?_
  have h := globalSectionOfModHom_eq (𝟙 (AdicSheaf.unit l Z))
  rw [Mod.id_hom', CategoryTheory.Functor.map_id, hone, globalSectionOfModHom_zero] at h
  exact h.symm

private lemma injective_Γ_map_upperStarCompIso {S Y Y' P : Scheme.{u}} {π : P ⟶ S}
    {w : Y' ⟶ Y} {z : S ⟶ Y} {z' : P ⟶ Y'} (hz : z' ≫ w = π ≫ z)
    (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    Function.Injective ((Sheaf.Γ _ (WeilCoefficients.{u} l)).map
      ((upperStarCompIso (WeilCoefficients.{u} l) hz).hom.app N ≫
      (π)^*[WeilCoefficients.{u} l].map (𝟙 ((z)^*[WeilCoefficients.{u} l].obj N)))).hom :=
  (ConcreteCategory.bijective_of_isIso _).1

private lemma globalSectionsTransport_one_apply {S Y Y' P : Scheme.{u}} {π : P ⟶ S}
    {w : Y' ⟶ Y} {z : S ⟶ Y} {z' : P ⟶ Y'} (hz : z' ≫ w = π ≫ z)
    (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) (x) :
    (globalSectionsTransport _ hz (𝟙 ((z)^*[WeilCoefficients.{u} l].obj N))).hom x =
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).map
        ((upperStarCompIso (WeilCoefficients.{u} l) hz).hom.app N ≫
        (π)^*[WeilCoefficients.{u} l].map (𝟙 ((z)^*[WeilCoefficients.{u} l].obj N)))).hom
      (((globalSectionsToUpperStar (WeilCoefficients.{u} l) z').app
        ((w)^*[WeilCoefficients.{u} l].obj N)).hom x) := by
  rw [globalSectionsTransport, ModuleCat.comp_apply]
  rfl

/-- The transport along `z' ≫ w = π ≫ z` of the section of an isomorphism `θ : ℚ̄_ℓ ≅ w^* N`
to the spectrum of a field is nonzero. -/
lemma globalSectionsTransport_globalSectionOfModHom_ne_zero {S Y Y' : Scheme.{u}} {L : Type u}
    [Field L] {π : Spec (.of L) ⟶ S} {w : Y' ⟶ Y} {z : S ⟶ Y} {z' : Spec (.of L) ⟶ Y'}
    (hz : z' ≫ w = π ≫ z) {N : AdicSheaf l Y} (θ : AdicSheaf.unit l Y' ≅ (w)^*ᵃ[l].obj N) :
    (globalSectionsTransport _ hz (𝟙 ((z)^*[WeilCoefficients.{u} l].obj N.X))).hom
      (globalSectionOfModHom θ.hom) ≠ 0 := by
  have hres : ((globalSectionsToUpperStar (WeilCoefficients.{u} l) z').app
      ((w)^*[WeilCoefficients.{u} l].obj N.X)).hom (globalSectionOfModHom θ.hom) =
      globalSectionOfModHom ((adicUpperStarUnitIso l z').inv ≫ (z')^*ᵃ[l].map θ.hom) :=
    globalSectionsToUpperStar_globalSectionOfModHom z' θ.hom
  rw [globalSectionsTransport_one_apply, hres]
  intro h
  have h' := injective_Γ_map_upperStarCompIso hz N.X (h.trans (map_zero _).symm)
  have hE : (adicUpperStarUnitIso l z').inv ≫ (z')^*ᵃ[l].map θ.hom =
      ((adicUpperStarUnitIso l z').symm ≪≫ (z')^*ᵃ[l].mapIso θ).hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [hE] at h'
  exact globalSectionOfModHom_ne_zero_of_iso _ h'

/-- **The twisted section.** Let `N` be an `ℓ`-adic sheaf on `Y`, `w : Y' ⟶ Y`, `g : Y' ⟶ Y'`
with `g ≫ w = w`, and `θ : ℚ̄_ℓ ≅ w^* N` a trivialisation whose section is multiplied by `χ`
under the germ along `g`. Let `z : S ⟶ Y`, `π : Spec L ⟶ S`, `z' : Spec L ⟶ Y'` with
`z' ≫ w = π ≫ z`, and `σ : Spec L ⟶ Spec L` with `σ ≫ π = π` and `σ ≫ z' = z' ≫ g`. Then the
transport of the section of `θ` is a nonzero section of `π^* z^* N` which the germ along `σ`
multiplies by `χ`. -/
lemma exists_ne_zero_factorGerm_eq_smul_of_twist {S Y Y' : Scheme.{u}} {L : Type u} [Field L]
    {π : Spec (.of L) ⟶ S} {σ : Spec (.of L) ⟶ Spec (.of L)} (hσ : σ ≫ π = π)
    {w : Y' ⟶ Y} {g : Y' ⟶ Y'} (hg : g ≫ w = w)
    {z : S ⟶ Y} {z' : Spec (.of L) ⟶ Y'} (hz : z' ≫ w = π ≫ z) (hσz : σ ≫ z' = z' ≫ g)
    {N : AdicSheaf l Y} (θ : AdicSheaf.unit l Y' ≅ (w)^*ᵃ[l].obj N) (χ : PadicAlgCl l)
    (hθ : (factorGerm (WeilCoefficients.{u} l) hg N.X).hom (globalSectionOfModHom θ.hom) =
      ULift.up χ • globalSectionOfModHom θ.hom) :
    ∃ e : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of L))) (WeilCoefficients.{u} l)).obj
        ((π)^*[WeilCoefficients.{u} l].obj ((z)^*[WeilCoefficients.{u} l].obj N.X)),
      e ≠ 0 ∧ (factorGerm (WeilCoefficients.{u} l) hσ _).hom e = ULift.up χ • e := by
  refine ⟨_, globalSectionsTransport_globalSectionOfModHom_ne_zero hz θ, ?_⟩
  rw [← ModuleCat.comp_apply, globalSectionsTransport_comp_factorGerm hσ hg hz hσz,
    ModuleCat.comp_apply,
    hθ, map_smul]

/-- **A sheaf trivialised with a twisted deck action is not a subquotient of a constant sheaf.**
Let `N` be an `ℓ`-adic sheaf on `Y`, `w : Y' ⟶ Y`, `g : Y' ⟶ Y'` with `g ≫ w = w`, and
`θ : ℚ̄_ℓ ≅ w^* N` a trivialisation whose section is multiplied by `χ ≠ 1` under the germ along
`g`. Let `z : S ⟶ Y`, `π : Spec L ⟶ S` for an algebraically closed field `L`,
`z' : Spec L ⟶ Y'` with `z' ≫ w = π ≫ z`, and `σ : Spec L ⟶ Spec L` with `σ ≫ π = π` and
`σ ≫ z' = z' ≫ g`. Then no subsheaf `B` of a constant sheaf `ℚ̄_ℓⁿ` on `S` surjects onto
`z^* N`.

The germ along `σ` fixes the sections of `π^* ℚ̄_ℓⁿ`, hence those of `π^* B`; they surject onto
those of `π^* z^* N` (`L` is algebraically closed), so the germ fixes the sections of
`π^* z^* N`, but it multiplies the transported section of `θ` by `χ`. -/
theorem not_epi_of_mono_biproduct_unit_of_twist {S Y Y' : Scheme.{u}} {L : Type u} [Field L]
    [IsAlgClosed L] {π : Spec (.of L) ⟶ S} {σ : Spec (.of L) ⟶ Spec (.of L)} (hσ : σ ≫ π = π)
    {w : Y' ⟶ Y} {g : Y' ⟶ Y'} (hg : g ≫ w = w)
    {z : S ⟶ Y} {z' : Spec (.of L) ⟶ Y'} (hz : z' ≫ w = π ≫ z) (hσz : σ ≫ z' = z' ≫ g)
    {N : AdicSheaf l Y} (θ : AdicSheaf.unit l Y' ≅ (w)^*ᵃ[l].obj N) {χ : PadicAlgCl l}
    (hχ : χ ≠ 1)
    (hθ : (factorGerm (WeilCoefficients.{u} l) hg N.X).hom (globalSectionOfModHom θ.hom) =
      ULift.up χ • globalSectionOfModHom θ.hom)
    {n : ℕ} {B : AdicSheaf l S} (m : B ⟶ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l S) [Mono m]
    (p : B ⟶ (z)^*ᵃ[l].obj N) [Epi p] : False := by
  obtain ⟨e, he0, he⟩ := exists_ne_zero_factorGerm_eq_smul_of_twist hσ hg hz hσz θ χ hθ
  -- lift `e` to a section `b` of `π^* B`; the objects are pinned to the forms in the types of `e`
  -- and `factorGerm_adicConstantSheaf_apply`, so that the kernel does not unfold `adicUpperStar`
  have hsurj : Function.Surjective ((geometricStalkFunctor l π).map p).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨b, hb⟩ : ∃ b : (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      ((π)^*[WeilCoefficients.{u} l].obj B.X),
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).map ((π)^*[WeilCoefficients.{u} l].map
        (Y := (z)^*[WeilCoefficients.{u} l].obj N.X) p.hom)).hom b = e := hsurj e
  -- the germ along `σ` fixes `b`, since it fixes the sections of `π^* ℚ̄_ℓⁿ`
  have hfixB : (factorGerm (WeilCoefficients.{u} l) hσ B.X).hom b = b := by
    obtain ⟨v, hv⟩ :=
      (bijective_globalSectionOfModHom ((π)^*ᵃ[l].obj B)).2
        ((factorGerm (WeilCoefficients.{u} l) hσ B.X).hom b - b)
    have hvi (i : Fin n) : v ≫ (π)^*ᵃ[l].map (m ≫ biproduct.π _ i) = 0 := by
      apply (bijective_globalSectionOfModHom _).1
      rw [globalSectionOfModHom_comp, hv, globalSectionOfModHom_zero, map_sub]
      have hn := congrArg (fun φ ↦ φ.hom b) (factorGerm_naturality (WeilCoefficients.{u} l) hσ
        (G := adicConstantSheaf l S) (m ≫ biproduct.π _ i).hom)
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hn
      rw [sub_eq_zero]
      exact hn.symm.trans (factorGerm_adicConstantSheaf_apply hσ _)
    have hvm : v ≫ (π)^*ᵃ[l].map m = 0 := by
      rw [← Category.comp_id m, ← biproduct.total, Preadditive.comp_sum, Functor.map_sum,
        Preadditive.comp_sum]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [← Category.assoc m, Functor.map_comp, ← Category.assoc, hvi,
        zero_comp]
    have hv0 : v = 0 := (cancel_mono ((π)^*ᵃ[l].map m)).1 (by rw [hvm, zero_comp])
    rw [← sub_eq_zero, ← hv, hv0, globalSectionOfModHom_zero]
  -- hence it fixes `e`
  have hfix : (factorGerm (WeilCoefficients.{u} l) hσ
      ((z)^*[WeilCoefficients.{u} l].obj N.X)).hom e = e := by
    have hn := congrArg (fun φ ↦ φ.hom b) (factorGerm_naturality (WeilCoefficients.{u} l) hσ
      (G := (z)^*[WeilCoefficients.{u} l].obj N.X) p.hom)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hfixB] at hn
    rw [← hb]
    exact hn
  rw [he] at hfix
  have h1 : (ULift.up χ - 1) • e = 0 := by rw [sub_smul, one_smul, hfix, sub_self]
  refine he0 ((smul_eq_zero.1 h1).resolve_left fun h ↦ hχ ?_)
  exact congrArg ULift.down (sub_eq_zero.1 h)

end AlgebraicGeometry.ProEtale
