/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseIrreducible
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyIrreducible

/-!
# Stalks of subsheaves of `ℓ`-adic sheaves

For an `ℓ`-adic sheaf `B` on a scheme `Y` and a geometric point `t : Spec Ω̄ ⟶ Y`, the stalk of a
subsheaf `P ⊆ B` is a subspace `P_t ⊆ B_t`
(`AlgebraicGeometry.ProEtale.adicStalkSubspace`), the image of the stalk of `P`. Since the stalk
functor is exact, `P ↦ P_t` is monotone and commutes with finite suprema
(`AlgebraicGeometry.ProEtale.adicStalkSubspace_finset_sup`). On a locally Noetherian scheme, a
finite supremum of lisse subsheaves of a lisse sheaf is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.underlying_finset_sup`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- The supremum of two subobjects is the image of the morphism from the coproduct. -/
theorem CategoryTheory.Subobject.mk_sup_mk {C : Type*} [Category C] [HasImages C]
    [HasBinaryCoproducts C] {A B B' : C} (f : B ⟶ A) (g : B' ⟶ A) [Mono f] [Mono g] :
    Subobject.mk f ⊔ Subobject.mk g = Subobject.mk (image.ι (coprod.desc f g)) :=
  rfl

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)

variable (l) in
/-- The stalk functor at a geometric point on `ℓ`-adic sheaves. -/
noncomputable abbrev adicStalkFunctor : AdicSheaf l Y ⥤ WeilCoefficients.{u} l :=
  AdicSheaf.forget Y ⋙ stalkFunctor l t

/-- The stalk functor is left exact. -/
instance : PreservesFiniteLimits (adicStalkFunctor l t) := by
  unfold adicStalkFunctor stalkFunctor
  infer_instance

/-- The stalk functor preserves epimorphisms: global sections on `Spec Ω̄` are exact. -/
instance : (adicStalkFunctor l t).PreservesEpimorphisms := by
  unfold adicStalkFunctor stalkFunctor
  infer_instance

/-- The stalk functor is additive. -/
instance : (adicStalkFunctor l t).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The `ℚ̄_ℓ`-linear map of stalks at a geometric point induced by a morphism of sheaves. -/
noncomputable abbrev adicStalkMap {A B : AdicSheaf l Y} (f : A ⟶ B) :
    (WeilCoefficients.toModuleCat l).obj ((adicStalkFunctor l t).obj A) →ₗ[PadicAlgCl l]
      (WeilCoefficients.toModuleCat l).obj ((adicStalkFunctor l t).obj B) :=
  ((WeilCoefficients.toModuleCat l).map ((adicStalkFunctor l t).map f)).hom

lemma adicStalkMap_comp {A B C : AdicSheaf l Y} (f : A ⟶ B) (g : B ⟶ C) :
    adicStalkMap t (f ≫ g) = adicStalkMap t g ∘ₗ adicStalkMap t f := by
  simp only [adicStalkMap, Functor.map_comp]
  rfl

lemma adicStalkMap_add {A B : AdicSheaf l Y} (f g : A ⟶ B) :
    adicStalkMap t (f + g) = adicStalkMap t f + adicStalkMap t g := by
  simp only [adicStalkMap, Functor.map_add]
  rfl

lemma adicStalkMap_zero (A B : AdicSheaf l Y) :
    adicStalkMap t (0 : A ⟶ B) = 0 := by
  simp only [adicStalkMap, Functor.map_zero]
  rfl

lemma surjective_adicStalkMap {A B : AdicSheaf l Y} (f : A ⟶ B) [Epi f] :
    Function.Surjective (adicStalkMap t f) :=
  (ModuleCat.epi_iff_surjective ((adicStalkFunctor l t).map f)).1 inferInstance

/-- The stalk functor preserves monomorphisms. -/
lemma injective_adicStalkMap {A B : AdicSheaf l Y} (f : A ⟶ B) [Mono f] :
    Function.Injective (adicStalkMap t f) :=
  (ModuleCat.mono_iff_injective ((adicStalkFunctor l t).map f)).1 inferInstance

lemma adicStalkMap_id (A : AdicSheaf l Y) : adicStalkMap t (𝟙 A) = LinearMap.id := by
  simp only [adicStalkMap, CategoryTheory.Functor.map_id]
  rfl

/-- The stalk `P_t ⊆ B_t` of a subsheaf `P ⊆ B` at a geometric point `t`: the image of the stalk
of `P`. -/
noncomputable def adicStalkSubspace {B : AdicSheaf l Y} (P : Subobject B) :
    Submodule (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((adicStalkFunctor l t).obj B)) :=
  LinearMap.range (adicStalkMap t P.arrow)

lemma range_adicStalkMap_epi_comp {A A' B : AdicSheaf l Y} (e : A' ⟶ A) [Epi e] (f : A ⟶ B) :
    LinearMap.range (adicStalkMap t (e ≫ f)) = LinearMap.range (adicStalkMap t f) := by
  rw [adicStalkMap_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (surjective_adicStalkMap t e)

lemma adicStalkSubspace_mk {A B : AdicSheaf l Y} (u : A ⟶ B) [Mono u] :
    adicStalkSubspace t (Subobject.mk u) = LinearMap.range (adicStalkMap t u) := by
  rw [adicStalkSubspace, ← Subobject.underlyingIso_hom_comp_eq_mk, range_adicStalkMap_epi_comp]

lemma adicStalkSubspace_mono {B : AdicSheaf l Y} {P Q : Subobject B} (h : P ≤ Q) :
    adicStalkSubspace t P ≤ adicStalkSubspace t Q := by
  rw [adicStalkSubspace, adicStalkSubspace, ← Subobject.ofLE_arrow h, adicStalkMap_comp]
  exact LinearMap.range_comp_le_range _ _

lemma adicStalkSubspace_top (B : AdicSheaf l Y) : adicStalkSubspace t (⊤ : Subobject B) = ⊤ := by
  rw [Subobject.top_eq_id, adicStalkSubspace_mk, adicStalkMap_id, LinearMap.range_id]

lemma adicStalkSubspace_bot (B : AdicSheaf l Y) : adicStalkSubspace t (⊥ : Subobject B) = ⊥ := by
  rw [adicStalkSubspace, Subobject.bot_arrow, adicStalkMap_zero, LinearMap.range_zero]

lemma range_adicStalkMap_coprodDesc {A A' B : AdicSheaf l Y} (a : A ⟶ B) (b : A' ⟶ B) :
    LinearMap.range (adicStalkMap t (coprod.desc a b)) ≤
      LinearMap.range (adicStalkMap t a) ⊔ LinearMap.range (adicStalkMap t b) := by
  have h : (biprod.isoCoprod A A').hom ≫ coprod.desc a b = biprod.desc a b := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [biprod_isoCoprod_hom]
  rw [← range_adicStalkMap_epi_comp t (biprod.isoCoprod A A').hom, h, biprod.desc_eq,
    adicStalkMap_add, adicStalkMap_comp, adicStalkMap_comp]
  exact (LinearMap.range_add_le _ _).trans
    (sup_le_sup (LinearMap.range_comp_le_range _ _) (LinearMap.range_comp_le_range _ _))

lemma adicStalkSubspace_sup {B : AdicSheaf l Y} (P Q : Subobject B) :
    adicStalkSubspace t (P ⊔ Q) = adicStalkSubspace t P ⊔ adicStalkSubspace t Q := by
  refine le_antisymm ?_ (sup_le (adicStalkSubspace_mono t le_sup_left)
    (adicStalkSubspace_mono t le_sup_right))
  rw [← Subobject.mk_arrow P, ← Subobject.mk_arrow Q, Subobject.mk_sup_mk,
    adicStalkSubspace_mk, adicStalkSubspace_mk, adicStalkSubspace_mk,
    ← range_adicStalkMap_epi_comp t (factorThruImage (coprod.desc P.arrow Q.arrow)), image.fac]
  exact range_adicStalkMap_coprodDesc t _ _

lemma adicStalkSubspace_finset_sup {B : AdicSheaf l Y} {ι : Type*} (s : Finset ι)
    (Q : ι → Subobject B) :
    adicStalkSubspace t (s.sup Q) = ⨆ i ∈ s, adicStalkSubspace t (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, adicStalkSubspace_bot, Finset.notMem_empty, iSup_false, iSup_bot]
  | insert i s hi ih => rw [Finset.sup_insert, adicStalkSubspace_sup, ih, Finset.iSup_insert]

/-- A supremum of two lisse subsheaves of a lisse sheaf on a locally Noetherian scheme is lisse:
it is the image of the morphism from their direct sum. -/
lemma IsAdicLisseSheaf.underlying_sup [IsLocallyNoetherian Y] {B : AdicSheaf l Y}
    (hB : IsAdicLisseSheaf B) {P Q : Subobject B}
    (hP : IsAdicLisseSheaf (Subobject.underlying.obj P))
    (hQ : IsAdicLisseSheaf (Subobject.underlying.obj Q)) :
    IsAdicLisseSheaf (Subobject.underlying.obj (P ⊔ Q)) := by
  have hPQ : IsAdicLisseSheaf (Subobject.underlying.obj P ⨿ Subobject.underlying.obj Q) :=
    (hP.biprod hQ).of_iso (biprod.isoCoprod _ _)
  have e : P ⊔ Q = Subobject.mk (image.ι (coprod.desc P.arrow Q.arrow)) := by
    rw [← Subobject.mk_sup_mk, Subobject.mk_arrow, Subobject.mk_arrow]
  rw [e]
  exact (hB.kernel_cokernel (hPQ.kernel_cokernel hB (coprod.desc P.arrow Q.arrow)).2
    (cokernel.π _)).1.of_iso
      ((Abelian.imageIsoImage _) ≪≫ (Subobject.underlyingIso _).symm)

/-- A finite supremum of lisse subsheaves of a lisse sheaf on a locally Noetherian scheme is
lisse. -/
lemma IsAdicLisseSheaf.underlying_finset_sup [IsLocallyNoetherian Y] {B : AdicSheaf l Y}
    (hB : IsAdicLisseSheaf B) {ι : Type*} (s : Finset ι) {Q : ι → Subobject B}
    (hQ : ∀ i ∈ s, IsAdicLisseSheaf (Subobject.underlying.obj (Q i))) :
    IsAdicLisseSheaf (Subobject.underlying.obj (s.sup Q)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact IsAdicLisseSheaf.of_isZero ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
  | insert i s hi ih =>
    rw [Finset.sup_insert]
    exact hB.underlying_sup (hQ i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ hQ j (Finset.mem_insert_of_mem hj))

/-- The reparametrisation `G_{a ≫ y} ≅ G_y` of stalks is natural in the sheaf `G`. -/
lemma reparamStalkIso_hom_naturality
    (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    {A B : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)} (f : A ⟶ B) :
    (stalkFunctor l (a.hom ≫ y)).map f ≫ (reparamStalkIso l a y B).hom =
      (reparamStalkIso l a y A).hom ≫ (stalkFunctor l y).map f := by
  simp only [reparamStalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    ← Functor.map_comp_assoc, NatTrans.naturality, Functor.comp_map, Category.assoc]
  rw [Functor.map_comp, Category.assoc]
  congr 1
  exact (globalSectionsUpperStarIso _ a).hom.naturality _


section Monodromy

variable {M : LisseMonodromy l Y Ω} {t}

/-- The stalk map of a morphism of lisse sheaves is that of the underlying `ℓ`-adic sheaves. -/
lemma lisseStalkMap_homMk {G H : LisseSheaf l Y} (f : G.obj ⟶ H.obj) :
    lisseStalkMap t (ObjectProperty.homMk f : G ⟶ H) = adicStalkMap t f :=
  rfl

/-- **Lisse subsheaves are determined by their stalks.** If the monodromy at `t` is an
equivalence, a lisse subsheaf `P` of a lisse sheaf `B` on a locally Noetherian scheme is contained
in a lisse subsheaf `Q` as soon as `P_t ⊆ Q_t`: the composite `P ⟶ B ⟶ B / Q` of lisse sheaves
vanishes on stalks at `t`. -/
lemma le_of_adicStalkSubspace_le (hM : M.IsEquivalenceAt t) [IsLocallyNoetherian Y]
    {B : AdicSheaf l Y} (hB : IsAdicLisseSheaf B) {P Q : Subobject B}
    (hP : IsAdicLisseSheaf (Subobject.underlying.obj P))
    (hQ : IsAdicLisseSheaf (Subobject.underlying.obj Q))
    (h : adicStalkSubspace t P ≤ adicStalkSubspace t Q) : P ≤ Q := by
  have hc : IsAdicLisseSheaf (cokernel Q.arrow) := (hQ.kernel_cokernel hB Q.arrow).2
  have e (v : (WeilCoefficients.toModuleCat l).obj ((adicStalkFunctor l t).obj
      (Subobject.underlying.obj P))) :
      adicStalkMap t (P.arrow ≫ cokernel.π Q.arrow) v = adicStalkMap t 0 v := by
    obtain ⟨w, hw⟩ := h (LinearMap.mem_range_self (adicStalkMap t P.arrow) v)
    rw [adicStalkMap_comp, LinearMap.comp_apply, ← hw, ← LinearMap.comp_apply, ← adicStalkMap_comp,
      cokernel.condition, adicStalkMap_zero, adicStalkMap_zero]
    rfl
  have h0 : (ObjectProperty.homMk (P.arrow ≫ cokernel.π Q.arrow) :
      (⟨_, hP⟩ : LisseSheaf l Y) ⟶ ⟨_, hc⟩) = ObjectProperty.homMk 0 :=
    hM.ext_of_lisseStalkMap (LinearMap.ext e)
  exact Subobject.le_of_comm (Abelian.monoLift Q.arrow P.arrow (congrArg (·.hom) h0))
    (Abelian.monoLift_comp _ _ _)

/-- **Irreducibility from the stalk.** If the monodromy at `t` is an equivalence, a lisse
subsheaf `P` of a lisse sheaf `B` on a locally Noetherian scheme is an irreducible local system
as soon as its stalk `P_t` is a nonzero irreducible subrepresentation of `B_t`. -/
lemma isIrreducibleAdicLocalSystem_of_adicStalkSubspace (hM : M.IsEquivalenceAt t)
    [IsLocallyNoetherian Y] {B : AdicSheaf l Y} (hB : IsAdicLisseSheaf B) {P : Subobject B}
    (hP : IsAdicLisseSheaf (Subobject.underlying.obj P)) (h0 : adicStalkSubspace t P ≠ ⊥)
    (hirr : ∀ D : Submodule (PadicAlgCl l) (LisseMonodromy.StalkSpace t (⟨B, hB⟩ : LisseSheaf l Y)),
      (∀ g, ∀ x ∈ D, M.rep t ⟨B, hB⟩ g x ∈ D) → D ≤ adicStalkSubspace t P →
        D = ⊥ ∨ D = adicStalkSubspace t P) :
    IsIrreducibleAdicLocalSystem (Subobject.underlying.obj P) := by
  refine ⟨hP, fun hz ↦ h0 ?_, fun H i hi hH ↦ ?_⟩
  · rw [adicStalkSubspace, hz.eq_of_src P.arrow 0, adicStalkMap_zero, LinearMap.range_zero]
  let j : (⟨H, hH⟩ : LisseSheaf l Y) ⟶ ⟨B, hB⟩ := ObjectProperty.homMk (i ≫ P.arrow)
  have hj : Function.Injective (adicStalkMap t (i ≫ P.arrow)) := injective_adicStalkMap t _
  have hinv (g : Aut (Scheme.FiniteEtale.fiber t)) :
      ∀ x ∈ LinearMap.range (adicStalkMap t (i ≫ P.arrow)), M.rep t ⟨B, hB⟩ g x ∈
        LinearMap.range (adicStalkMap t (i ≫ P.arrow)) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨M.rep t ⟨H, hH⟩ g y, M.rep_naturality t j g y⟩
  have hle : LinearMap.range (adicStalkMap t (i ≫ P.arrow)) ≤ adicStalkSubspace t P := by
    rw [adicStalkMap_comp, LinearMap.range_comp]
    exact LinearMap.map_le_range
  rcases hirr _ hinv hle with h | h
  · left
    have : Subsingleton (LisseMonodromy.StalkSpace t (⟨H, hH⟩ : LisseSheaf l Y)) :=
      ⟨fun v w ↦ hj (by
        rw [LinearMap.range_eq_bot.1 h]
        rfl)⟩
    exact hM.isZero_of_subsingleton ⟨H, hH⟩
  · right
    have hbij : Function.Bijective (lisseStalkMap t
        (ObjectProperty.homMk i : (⟨H, hH⟩ : LisseSheaf l Y) ⟶ ⟨_, hP⟩)) := by
      refine ⟨injective_adicStalkMap t i, fun y ↦ ?_⟩
      obtain ⟨z, hz⟩ : adicStalkMap t P.arrow y ∈
          LinearMap.range (adicStalkMap t (i ≫ P.arrow)) := by
        rw [h]
        exact LinearMap.mem_range_self _ y
      refine ⟨z, injective_adicStalkMap t P.arrow ?_⟩
      exact (LinearMap.congr_fun (adicStalkMap_comp t i P.arrow) z).symm.trans hz
    have := hM.isIso_of_bijective _ hbij
    exact (ObjectProperty.ι _).map_isIso (ObjectProperty.homMk i :
      (⟨H, hH⟩ : LisseSheaf l Y) ⟶ ⟨_, hP⟩)

/-- **Subrepresentations of a stalk come from lisse subsheaves.** If the monodromy at `t` is an
equivalence, every subrepresentation of the stalk `B_t` of a lisse sheaf `B` on a locally
Noetherian scheme is the stalk of a lisse subsheaf. -/
lemma exists_adicStalkSubspace_eq (hM : M.IsEquivalenceAt t) [IsLocallyNoetherian Y]
    {B : AdicSheaf l Y} (hB : IsAdicLisseSheaf B)
    (C : Submodule (PadicAlgCl l) (LisseMonodromy.StalkSpace t (⟨B, hB⟩ : LisseSheaf l Y)))
    (hC : ∀ g, ∀ x ∈ C, M.rep t ⟨B, hB⟩ g x ∈ C) :
    ∃ P : Subobject B, IsAdicLisseSheaf (Subobject.underlying.obj P) ∧
      adicStalkSubspace t P = C := by
  obtain ⟨G', a, hinj, hrange⟩ := hM.exists_hom_range_eq ⟨C, fun g _ hx ↦ hC g _ hx⟩
  have := hM.mono_of_injective a hinj
  exact ⟨Subobject.mk a.hom, G'.property.of_iso (Subobject.underlyingIso a.hom).symm,
    (adicStalkSubspace_mk t a.hom).trans hrange⟩

end Monodromy
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilCoefficients

variable {l : ℕ} [Fact l.Prime]

lemma linearEquivOfIso_trans {M N P : WeilCoefficients.{u} l} (e : M ≅ N) (e' : N ≅ P) :
    linearEquivOfIso (e ≪≫ e') = (linearEquivOfIso e).trans (linearEquivOfIso e') :=
  LinearEquiv.ext fun _ ↦ rfl

lemma linearEquivOfIso_symm {M N : WeilCoefficients.{u} l} (e : M ≅ N) :
    linearEquivOfIso e.symm = (linearEquivOfIso e).symm :=
  LinearEquiv.ext fun x ↦ (linearEquivOfIso e).injective (by
    rw [LinearEquiv.apply_symm_apply, linearEquivOfIso_apply, linearEquivOfIso_apply]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id) x)

lemma linearEquivOfIso_apply_eq_toModuleCat_map {M N : WeilCoefficients.{u} l} (e : M ≅ N)
    (x : (toModuleCat l).obj M) :
    linearEquivOfIso e x = ((toModuleCat l).map e.hom).hom x :=
  rfl

end AlgebraicGeometry.WeilCoefficients
