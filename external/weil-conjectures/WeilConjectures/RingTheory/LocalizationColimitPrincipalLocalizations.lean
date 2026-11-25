/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# A localization as a filtered colimit of principal localizations

Source: Stacks Project, Algebra, Lemma 10.9.9, Tag 00CR, specialized to the ring itself
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- Stacks Project, Algebra, Tag 00CR, in the ring case.
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
The divisibility preorder on `S` is directed, and hence filtered. The maps between the
principal localizations are specified on every fraction, for every choice of the factor `h`.
The functor and its chosen colimit `colimit F` are identified with these rings and maps by
the displayed isomorphisms; these merely transport the diagram, rather than change its objects.

Proof (Stacks 00CR's universal-property hint, specialized to rings):
1. Use divisibility for the preorder. The product `f * g` is a common upper bound,
   and `1 ∈ S`, so the associated category is filtered.
2. Construct `rho` by `IsLocalization.Away.lift`: a divisor of the unit `g` is a unit.
   The fraction formula follows by multiplying by the image of `g^n` and using
   `IsLocalization.mk'_spec`; the construction does not choose a factor `h`.
3. Construct `kappa` by the same universal property, since every element of `S` becomes
   a unit. Its fraction formula follows from `mk'_spec` as well.
4. Ring homomorphisms out of a localization are determined on the original ring.
   This proves the identity, composition, and cocone compatibility equations.
5. For an arbitrary cocone, compose its component at `1` with the map from `P`.
   Naturality along `1 ≤ f` identifies this composite with the one at every `f`.
   Thus it sends `f` to a unit, witnessed by the component at `f`, and extends to
   `S⁻¹P` by `IsLocalization.lift`. Extensionality on `P` proves factorization
   through every component and uniqueness, giving a colimit cocone.
6. Take the identity object isomorphisms for the diagram, and use uniqueness of
   colimits to identify its chosen colimit with `S⁻¹P`, preserving the coprojections. -/
theorem localization_colimit_principalLocalizations
    (P : Type u) [CommRing P] (S : Submonoid P) :
    ∃ p : Preorder S,
      letI : Preorder S := p
      (∀ f g : S, f ≤ g ↔ ∃ h : P, (g : P) = (f : P) * h) ∧
      (∀ f g : S, f ≤ f * g ∧ g ≤ f * g) ∧
      IsDirected S (· ≤ ·) ∧ IsFiltered S ∧
      ∃ (rho : ∀ f g : S, f ≤ g →
          Localization.Away (f : P) →+* Localization.Away (g : P))
        (kappa : ∀ f : S, Localization.Away (f : P) →+* LocalizedModule S P),
        (∀ (f g : S) (l : f ≤ g) (h a : P) (n : ℕ),
          (g : P) = (f : P) * h →
          rho f g l (IsLocalization.mk' (M := Submonoid.powers (f : P))
            (Localization.Away (f : P)) a
            ⟨(f : P) ^ n, ⟨n, rfl⟩⟩) =
          IsLocalization.mk' (M := Submonoid.powers (g : P))
            (Localization.Away (g : P)) (a * h ^ n)
            ⟨(g : P) ^ n, ⟨n, rfl⟩⟩) ∧
        (∀ (f : S) (l : f ≤ f), rho f f l = RingHom.id _) ∧
        (∀ (f g k : S) (l : f ≤ g) (m : g ≤ k),
          (rho g k m).comp (rho f g l) = rho f k (le_trans l m)) ∧
        (∀ (f : S) (a : P) (n : ℕ),
          kappa f (IsLocalization.mk' (M := Submonoid.powers (f : P))
            (Localization.Away (f : P)) a
            ⟨(f : P) ^ n, ⟨n, rfl⟩⟩) = LocalizedModule.mk a (f ^ n)) ∧
        (∀ (f g : S) (l : f ≤ g), (kappa g).comp (rho f g l) = kappa f) ∧
        (∀ f : S, (kappa f).comp (algebraMap P (Localization.Away (f : P))) =
          algebraMap P (LocalizedModule S P)) ∧
        ∃ (F : S ⥤ CommRingCat.{u})
          (e : ∀ f : S, F.obj f ≅ CommRingCat.of (Localization.Away (f : P)))
          (eL : colimit F ≅ CommRingCat.of (LocalizedModule S P)),
          (∀ (f g : S) (l : f ≤ g),
            (e f).inv ≫ F.map (homOfLE l) ≫ (e g).hom = ofHom (rho f g l)) ∧
          (∀ f : S, (e f).inv ≫ colimit.ι F f ≫ eL.hom = ofHom (kappa f)) := by
  classical
  let p : Preorder S :=
    { le := fun f g => (f : P) ∣ (g : P)
      le_refl := fun f => dvd_refl _
      le_trans := fun _ _ _ h k => h.trans k }
  refine ⟨p, ?_⟩
  let : Preorder S := p
  have bounds (f g : S) : f ≤ f * g ∧ g ≤ f * g :=
    ⟨⟨g, rfl⟩, ⟨f, mul_comm _ _⟩⟩
  have directed : IsDirected S (· ≤ ·) :=
    ⟨fun f g => ⟨f * g, (bounds f g).1, (bounds f g).2⟩⟩
  let rho (f g : S) (l : f ≤ g) :
      Localization.Away (f : P) →+* Localization.Away (g : P) :=
    IsLocalization.Away.lift (f : P)
      (IsLocalization.Away.isUnit_of_dvd (g : P) l)
  let kappa (f : S) : Localization.Away (f : P) →+* LocalizedModule S P :=
    IsLocalization.Away.lift (f : P) (IsLocalization.map_units (LocalizedModule S P) f)
  have hrho (f g : S) (l : f ≤ g) (a : P) :
      rho f g l (algebraMap P _ a) = algebraMap P _ a :=
    IsLocalization.Away.lift_eq _ _ _
  have hkappa (f : S) (a : P) :
      kappa f (algebraMap P _ a) = algebraMap P _ a :=
    IsLocalization.Away.lift_eq _ _ _
  have hid (f : S) (l : f ≤ f) : rho f f l = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f : P))
    ext a
    exact hrho f f l a
  have hcomp (f g k : S) (l : f ≤ g) (m : g ≤ k) :
      (rho g k m).comp (rho f g l) = rho f k (le_trans l m) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f : P))
    ext a
    simp only [RingHom.comp_apply, hrho]
  have hcompat (f g : S) (l : f ≤ g) :
      (kappa g).comp (rho f g l) = kappa f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f : P))
    ext a
    simp only [RingHom.comp_apply, hrho, hkappa]
  refine ⟨fun _ _ => Iff.rfl, bounds, directed, inferInstance, rho, kappa,
    ?_, hid, hcomp, ?_, hcompat, ?_, ?_⟩
  · intro f g l h a n hfg
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    change rho f g l _ * algebraMap P _ ((g : P) ^ n) =
      algebraMap P _ (a * h ^ n)
    have hpow : (g : P) ^ n = (f : P) ^ n * h ^ n := by rw [hfg, mul_pow]
    rw [hpow, map_mul, ← mul_assoc, ← hrho f g l ((f : P) ^ n),
      ← map_mul, IsLocalization.mk'_spec, hrho f g l a, ← map_mul]
  · intro f a n
    change kappa f _ = Localization.mk a (f ^ n)
    rw [Localization.mk_eq_mk']
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    change kappa f _ * algebraMap P _ ((f : P) ^ n) = algebraMap P _ a
    rw [← hkappa f ((f : P) ^ n), ← map_mul, IsLocalization.mk'_spec, hkappa]
  · intro f
    ext a
    exact hkappa f a
  · let F : S ⥤ CommRingCat.{u} :=
      { obj := fun f => .of (Localization.Away (f : P))
        map := fun {f g} l => ofHom (rho f g (leOfHom l))
        map_id := fun f => by
          apply CommRingCat.hom_ext
          exact hid f (le_refl f)
        map_comp := fun {f g k} l m => by
          apply CommRingCat.hom_ext
          exact (hcomp f g k (leOfHom l) (leOfHom m)).symm }
    let c : Cocone F :=
      { pt := .of (LocalizedModule S P)
        ι :=
          { app := fun f => ofHom (kappa f)
            naturality := fun {f g} l => by
              apply CommRingCat.hom_ext
              change (kappa g).comp (rho f g (leOfHom l)) = kappa f
              exact hcompat f g (leOfHom l) } }
    let base (s : Cocone F) : P →+* s.pt :=
      (s.ι.app (1 : S)).hom.comp (algebraMap P (Localization.Away (1 : P)))
    have hbase (s : Cocone F) (f : S) :
        (s.ι.app f).hom.comp (algebraMap P (Localization.Away (f : P))) = base s := by
      ext a
      have l : (1 : S) ≤ f := ⟨(f : P), (one_mul _).symm⟩
      have w := ConcreteCategory.congr_hom (s.w (homOfLE l))
        (algebraMap P (Localization.Away (1 : P)) a)
      change (s.ι.app f).hom (rho 1 f l (algebraMap P _ a)) = base s a at w
      rw [hrho 1 f l a] at w
      exact w
    have hunits (s : Cocone F) (f : S) : IsUnit (base s (f : P)) := by
      rw [← hbase s f]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f : P))
        (f : P)).map (s.ι.app f).hom
    have hc : IsColimit c :=
      { desc := fun s => ofHom (IsLocalization.lift (S := LocalizedModule S P) (hunits s))
        fac := fun s f => by
          apply CommRingCat.hom_ext
          apply IsLocalization.ringHom_ext (Submonoid.powers (f : P))
          ext a
          change IsLocalization.lift (hunits s) (kappa f (algebraMap P _ a)) =
            (s.ι.app f).hom (algebraMap P _ a)
          rw [hkappa, IsLocalization.lift_eq]
          exact (RingHom.congr_fun (hbase s f) a).symm
        uniq := fun s m hm => by
          apply CommRingCat.hom_ext
          apply IsLocalization.ringHom_ext S
          ext a
          change m.hom (algebraMap P (LocalizedModule S P) a) =
            IsLocalization.lift (hunits s) (algebraMap P (LocalizedModule S P) a)
          rw [IsLocalization.lift_eq]
          have w := ConcreteCategory.congr_hom (hm (1 : S))
            (algebraMap P (Localization.Away (1 : P)) a)
          change m.hom (kappa 1 (algebraMap P _ a)) = base s a at w
          rw [hkappa] at w
          exact w }
    refine ⟨F, fun f => Iso.refl _,
      (colimit.isColimit F).coconePointUniqueUpToIso hc, ?_, ?_⟩
    · intro f g l
      simp [F]
    · intro f
      change 𝟙 _ ≫ colimit.ι F f ≫
        ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom = c.ι.app f
      rw [Category.id_comp]
      exact (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc f

end CommRingCat
