/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerArtinian
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-!
# Towers of finite locally constant sheaves are Mittag-Leffler

Let `Y` be a connected scheme with a geometric point `s` and `Λ` a finite ring.

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.isIso_of_isIso_sheafFiber_map`: a
  morphism of finite locally constant sheaves of `Λ`-modules which is an isomorphism on the
  stalk at `s` is an isomorphism (Galois correspondence,
  `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf`);
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.imageSubobject`: images of morphisms
  of finite locally constant sheaves are finite locally constant;
- `AlgebraicGeometry.Scheme.imagesStabilize_of_isFiniteLocallyConstantSheaf`,
  `AlgebraicGeometry.Scheme.isMittagLefflerTower_of_isFiniteLocallyConstantSheaf`: in a tower
  of finite locally constant sheaves the images stabilise (their stalks at `s` form a decreasing
  chain in a finite module), so the tower is Mittag-Leffler;
- `Scheme.isMittagLefflerTower_comp_comparisonUpperStar_of_isFiniteLocallyConstantSheaf`:
  so is its comparison pullback `ν^*` to the pro-étale site.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **The stalk at one geometric point detects isomorphisms of finite locally constant sheaves**
on a connected scheme: by the Galois correspondence the stalk functor is, on finite locally
constant sheaves, an equivalence onto finite continuous representations of `π₁` followed by
the forgetful functor, which reflects isomorphisms. -/
theorem IsFiniteLocallyConstantSheaf.isIso_of_isIso_sheafFiber_map
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)
    (hG : IsFiniteLocallyConstantSheaf G) (φ : F ⟶ G)
    [IsIso ((pointSmallEtale s).sheafFiber.map φ)] : IsIso φ := by
  obtain ⟨Gp, e, ⟨i⟩⟩ := Scheme.exists_equivalence_isFiniteLocallyConstantSheaf Y s Λ
  let φ' : (⟨F, hF⟩ : ObjectProperty.FullSubcategory
      (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        Scheme.IsFiniteLocallyConstantSheaf F)) ⟶ ⟨G, hG⟩ := ObjectProperty.homMk φ
  have h1 : IsIso ((ObjectProperty.ι _ ⋙ (pointSmallEtale s).sheafFiber).map φ') :=
    inferInstanceAs (IsIso ((pointSmallEtale s).sheafFiber.map φ))
  have h2 := (NatIso.isIso_map_iff i φ').2 h1
  have h3 : IsIso (e.functor.map φ') := by
    have : IsIso ((forget₂ (Rep.{u + 1} Λ Gp) (ModuleCat.{u + 1} Λ)).map
        ((ObjectProperty.ι _).map (e.functor.map φ'))) := h2
    have : IsIso ((ObjectProperty.ι _).map (e.functor.map φ')) :=
      isIso_of_reflects_iso _ (forget₂ (Rep.{u + 1} Λ Gp) (ModuleCat.{u + 1} Λ))
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  have : IsIso φ' := isIso_of_reflects_iso _ e.functor
  exact inferInstanceAs (IsIso ((ObjectProperty.ι _).map φ'))

omit [ConnectedSpace Y] [Finite Λ] in
/-- **The image of a morphism of finite locally constant sheaves is finite locally constant**,
being the kernel of the cokernel. -/
lemma IsFiniteLocallyConstantSheaf.imageSubobject [IsNoetherianRing Λ]
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ G)
    [IsFiniteLocallyConstantSheaf F] [IsFiniteLocallyConstantSheaf G] :
    IsFiniteLocallyConstantSheaf (Subobject.underlying.obj (Limits.imageSubobject f)) := by
  have := IsFiniteLocallyConstantSheaf.cokernel f
  have := IsFiniteLocallyConstantSheaf.kernel (cokernel.π f)
  exact IsFiniteLocallyConstantSheaf.of_iso
    ((Abelian.imageIsoImage f).trans (imageSubobjectIso f).symm)

section Stalk

variable {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

omit [ConnectedSpace Y] [Finite Λ] in
/-- The stalk of the inclusion of the image has the same range as the stalk of the morphism. -/
lemma range_sheafFiber_map_imageSubobject_arrow (f : F ⟶ G) :
    LinearMap.range ((pointSmallEtale s).sheafFiber.map (Limits.imageSubobject f).arrow).hom =
      LinearMap.range ((pointSmallEtale s).sheafFiber.map f).hom := by
  have hfac := congrArg (pointSmallEtale s).sheafFiber.map (imageSubobject_arrow_comp f)
  rw [Functor.map_comp] at hfac
  have hsurj : Function.Surjective
      ((pointSmallEtale s).sheafFiber.map (factorThruImageSubobject f)).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, by rw [← hfac]; rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, by rw [← hfac]; rfl⟩

end Stalk

include s in
open CategoryTheory.Limits.ArtinianTower in
/-- **Images stabilise in a tower of finite locally constant sheaves on a connected scheme**,
for a finite coefficient ring: the stalks at one geometric point of the images form a
decreasing chain of submodules of a finite module, which stabilises, and an inclusion of finite
locally constant sheaves which is an isomorphism on that stalk is an isomorphism. -/
theorem imagesStabilize_of_isFiniteLocallyConstantSheaf
    (G : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [hG : ∀ n : ℕ, IsFiniteLocallyConstantSheaf (G.obj (op n))] : ImagesStabilize G := by
  intro n
  let St := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : Module.Finite Λ (St.obj (G.obj (op n))) := (ModuleCat.isFinitelyGenerated_iff _).1
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := G.obj (op n)) Ω s)
  have : Finite (St.obj (G.obj (op n))) := Module.finite_of_finite Λ
  have : IsArtinian Λ (St.obj (G.obj (op n))) := isArtinian_of_finite
  have hrange {k k' : ℕ} (h : n ≤ k) (h' : k ≤ k') :
      LinearMap.range (St.map (tr G (h.trans h'))).hom ≤ LinearMap.range (St.map (tr G h)).hom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(St.map (tr G h')).hom x, ?_⟩
    rw [← tr_comp G h h', Functor.map_comp]
    rfl
  let f : ℕ →o (Submodule Λ (St.obj (G.obj (op n))))ᵒᵈ :=
    ⟨fun k ↦ OrderDual.toDual (LinearMap.range (St.map (tr G (n.le_add_right k))).hom),
      fun k k' hk ↦ hrange (n.le_add_right k) (show n + k ≤ n + k' by lia)⟩
  obtain ⟨K, hK⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨n + K, n.le_add_right K, fun m hm ↦ le_antisymm (im_antitone G _ hm) ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ((n.le_add_right K).trans hm)
  have hk : LinearMap.range (St.map (tr G (n.le_add_right k))).hom =
      LinearMap.range (St.map (tr G (n.le_add_right K))).hom :=
    congrArg OrderDual.ofDual (hK k (by lia)).symm
  have hle := im_antitone G (n.le_add_right K) hm
  let ι := Subobject.ofLE _ _ hle
  have h₁ := IsFiniteLocallyConstantSheaf.imageSubobject (tr G ((n.le_add_right K).trans hm))
  have h₂ := IsFiniteLocallyConstantSheaf.imageSubobject (tr G (n.le_add_right K))
  have hι : IsIso (St.map ι) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨(ModuleCat.mono_iff_injective _).1 inferInstance, fun y ↦ ?_⟩
    have hy : (St.map (im G (n.le_add_right K)).arrow).hom y ∈
        LinearMap.range (St.map (tr G ((n.le_add_right K).trans hm))).hom := by
      rw [show (n.le_add_right K).trans hm = n.le_add_right k from rfl, hk,
        ← range_sheafFiber_map_imageSubobject_arrow]
      exact ⟨y, rfl⟩
    rw [← range_sheafFiber_map_imageSubobject_arrow] at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, (ModuleCat.mono_iff_injective (St.map (im G (n.le_add_right K)).arrow)).1
      inferInstance ?_⟩
    rw [← hx, ← ConcreteCategory.comp_apply, ← Functor.map_comp, Subobject.ofLE_arrow]
  have := IsFiniteLocallyConstantSheaf.isIso_of_isIso_sheafFiber_map s
    (hF := h₁) (hG := h₂) ι
  exact Subobject.le_of_comm (inv ι) (by rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow])

include s in
/-- **Towers of finite locally constant sheaves on a connected scheme are Mittag-Leffler**
(finite coefficient ring). -/
theorem isMittagLefflerTower_of_isFiniteLocallyConstantSheaf
    (G : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (G.obj (op n))] : IsMittagLefflerTower G :=
  isMittagLefflerTower_of_imagesStabilize (imagesStabilize_of_isFiniteLocallyConstantSheaf s G)

include s in
/-- **The comparison pullback of a tower of finite locally constant sheaves on a connected scheme
is Mittag-Leffler** on the pro-étale site, `ν^*` being exact. -/
theorem isMittagLefflerTower_comp_comparisonUpperStar_of_isFiniteLocallyConstantSheaf
    (G : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (G.obj (op n))] :
    IsMittagLefflerTower (G ⋙ ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y) :=
  have := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) Y).isLeftAdjoint
  (isMittagLefflerTower_of_isFiniteLocallyConstantSheaf s G).map _

omit [IsSepClosed Ω] in
/-- **Towers of finite locally constant sheaves on a connected nonempty scheme are
Mittag-Leffler** (finite coefficient ring), the geometric point being the algebraic closure of a
residue field. -/
theorem isMittagLefflerTower_of_isFiniteLocallyConstantSheaf_of_nonempty [Nonempty Y]
    (G : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (G.obj (op n))] : IsMittagLefflerTower G :=
  isMittagLefflerTower_of_isFiniteLocallyConstantSheaf
    (Y.algClosurePoint (Classical.arbitrary Y)) G

end AlgebraicGeometry.Scheme
