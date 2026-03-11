;;; atp-dungeon.el --- FOL-based dungeon crawler -*- lexical-binding: t; -*-

;; Copyright (C) 2024 Andrew Dougherty
;; License: GPL-3.0-or-later

;;; Commentary:
;;
;; A text-based dungeon crawl game where the game world state is
;; maintained as a first-order logic knowledge base, and the ATP
;; (emacs-atp.el) is used for reasoning about actions, items, puzzles,
;; and NPC interactions.
;;
;; Theme: Irish mythology - the Tuatha Dé Danann, Fomorians,
;; the Dagda's cauldron, the Sword of Light, etc.
;;
;; Architecture:
;;   - Game state = FOL knowledge base (list of formulas)
;;   - Actions are derived by the ATP from rules + current state
;;   - Puzzles require logical deduction
;;   - NPC dialog driven by what's provable from the KB

;;; Code:

(require 'cl-lib)

;; Load the ATP
(unless (featurep 'emacs-atp)
  (load-file (expand-file-name "emacs-atp.el"
                                (or (and load-file-name (file-name-directory load-file-name))
                                    default-directory))))

;; ============================================================
;; Game state
;; ============================================================

(defvar dungeon--kb nil "The game's knowledge base.")
(defvar dungeon--rules nil "Permanent rules (implications).")
(defvar dungeon--history nil "Command history.")
(defvar dungeon--turn 0 "Current turn number.")
(defvar dungeon--buffer "*Dún na Sí*" "Game buffer name.")

;; ============================================================
;; KB operations
;; ============================================================

(defun dungeon--assert (fact)
  "Assert FACT into the game KB."
  (unless (member fact dungeon--kb)
    (push fact dungeon--kb)))

(defun dungeon--retract (fact)
  "Remove FACT from the game KB."
  (setq dungeon--kb (cl-remove fact dungeon--kb :test #'equal)))

(defun dungeon--query (goal &optional max-iter)
  "Query if GOAL is provable from KB + rules."
  (prove goal (append dungeon--rules dungeon--kb) nil (or max-iter 500)))

(defun dungeon--assert-rule (rule)
  "Add a permanent RULE."
  (unless (member rule dungeon--rules)
    (push rule dungeon--rules)))

;; ============================================================
;; Display
;; ============================================================

(defun dungeon--emit (text &optional face)
  "Print TEXT to the game buffer with optional FACE."
  (with-current-buffer (get-buffer-create dungeon--buffer)
    (goto-char (point-max))
    (let ((start (point)))
      (insert text "\n")
      (when face
        (put-text-property start (point) 'face face)))))

(defun dungeon--emit-header (text)
  (dungeon--emit (format "\n═══ %s ═══" text) 'bold))

(defun dungeon--emit-room (text)
  (dungeon--emit text 'font-lock-function-name-face))

(defun dungeon--emit-item (text)
  (dungeon--emit (format "  ✦ %s" text) 'font-lock-constant-face))

(defun dungeon--emit-npc (text)
  (dungeon--emit text 'font-lock-string-face))

(defun dungeon--emit-action (text)
  (dungeon--emit (format "→ %s" text) 'font-lock-keyword-face))

(defun dungeon--emit-fail (text)
  (dungeon--emit text 'font-lock-warning-face))

(defun dungeon--emit-lore (text)
  (dungeon--emit (format "  « %s »" text) 'font-lock-doc-face))

;; ============================================================
;; World rules (FOL implications)
;; ============================================================

(defun dungeon--init-rules ()
  "Initialize the permanent game rules."
  (setq dungeon--rules nil)

  ;; --- Movement rules ---
  ;; If player is at X and X connects to Y and path is not blocked,
  ;; the player can move. (We check these procedurally but the
  ;; ATP validates preconditions.)

  ;; --- Item interaction rules ---
  ;; If player has key and door is locked, player can unlock
  (dungeon--assert-rule
   '(forall (k) (forall (d)
     (implies (and (has player k) (key-for k d) (locked d))
              (can-unlock player d)))))

  ;; If player has a light source, player can see in dark rooms
  (dungeon--assert-rule
   '(forall (x)
     (implies (and (has player x) (light-source x))
              (player-has-light))))

  ;; Dark rooms require light
  (dungeon--assert-rule
   '(forall (r)
     (implies (and (at player r) (dark r) (player-has-light))
              (can-see-in r))))

  ;; Weapons are effective against certain enemies
  (dungeon--assert-rule
   '(forall (w) (forall (e)
     (implies (and (has player w) (weapon w) (effective-against w e))
              (can-fight player e)))))

  ;; The Sword of Light (Claiomh Solais) is effective against Fomorians
  (dungeon--assert-rule
   '(forall (e)
     (implies (and (has player sword-of-light) (fomorian e))
              (can-fight player e))))

  ;; The Dagda's Cauldron heals
  (dungeon--assert-rule
   '(implies (has player cauldron-of-dagda)
             (can-heal player)))

  ;; The Stone of Destiny reveals truth
  (dungeon--assert-rule
   '(implies (and (has player lia-fail) (at player throne-room))
             (reveals-truth lia-fail)))

  ;; Sacred items combine for power
  (dungeon--assert-rule
   '(implies (and (has player sword-of-light)
                  (has player cauldron-of-dagda)
                  (has player lia-fail)
                  (has player spear-of-lugh))
             (has-four-treasures player)))

  ;; Four treasures banish the Fomorian King
  (dungeon--assert-rule
   '(implies (and (has-four-treasures player)
                  (at player great-hall))
             (can-banish player balor))))

;; ============================================================
;; World map and initialization
;; ============================================================

(defun dungeon--init-world ()
  "Set up the initial game world."
  (setq dungeon--kb nil)
  (setq dungeon--turn 0)
  (setq dungeon--history nil)

  ;; --- Rooms ---
  (dolist (r '(entrance-cave crystal-cavern forge
               mushroom-grove underground-lake dark-passage
               throne-room great-hall treasury hidden-shrine))
    (dungeon--assert `(room ,r)))

  ;; --- Connections (bidirectional) ---
  (dolist (conn '((entrance-cave crystal-cavern)
                  (crystal-cavern forge)
                  (crystal-cavern mushroom-grove)
                  (mushroom-grove underground-lake)
                  (underground-lake dark-passage)
                  (dark-passage throne-room)
                  (throne-room great-hall)
                  (forge treasury)
                  (crystal-cavern hidden-shrine)))
    (dungeon--assert `(connects ,(car conn) ,(cadr conn)))
    (dungeon--assert `(connects ,(cadr conn) ,(car conn))))

  ;; --- Dark rooms ---
  (dungeon--assert '(dark dark-passage))
  (dungeon--assert '(dark treasury))

  ;; --- Locked doors ---
  (dungeon--assert '(locked treasury))

  ;; --- Player start ---
  (dungeon--assert '(at player entrance-cave))
  (dungeon--assert '(alive player))

  ;; --- Items in rooms ---
  (dungeon--assert '(at-room torch entrance-cave))
  (dungeon--assert '(light-source torch))

  (dungeon--assert '(at-room rusty-key mushroom-grove))
  (dungeon--assert '(key-for rusty-key treasury))

  (dungeon--assert '(at-room sword-of-light treasury))
  (dungeon--assert '(weapon sword-of-light))

  (dungeon--assert '(at-room cauldron-of-dagda hidden-shrine))
  (dungeon--assert '(at-room lia-fail throne-room))
  (dungeon--assert '(at-room spear-of-lugh forge))
  (dungeon--assert '(weapon spear-of-lugh))

  (dungeon--assert '(at-room ancient-scroll crystal-cavern))
  (dungeon--assert '(at-room silver-coin mushroom-grove))

  ;; --- NPCs ---
  (dungeon--assert '(at-room brigid crystal-cavern))
  (dungeon--assert '(npc brigid))
  (dungeon--assert '(friendly brigid))

  (dungeon--assert '(at-room fomorian-guard dark-passage))
  (dungeon--assert '(npc fomorian-guard))
  (dungeon--assert '(fomorian fomorian-guard))
  (dungeon--assert '(hostile fomorian-guard))

  (dungeon--assert '(at-room balor great-hall))
  (dungeon--assert '(npc balor))
  (dungeon--assert '(fomorian balor))
  (dungeon--assert '(hostile balor))

  ;; --- Room descriptions ---
  (dungeon--assert '(description entrance-cave
    "A damp cave mouth opens before you. Stalactites drip with ancient water. The air smells of earth and iron. Ogham script is carved into the walls."))
  (dungeon--assert '(description crystal-cavern
    "The cavern opens into a breathtaking space. Crystals of every hue grow from floor and ceiling, casting prismatic light. A gentle hum resonates."))
  (dungeon--assert '(description forge
    "An ancient forge, still warm. The anvil bears the mark of Goibniu, smith of the Tuatha Dé Danann. Embers glow in the darkness."))
  (dungeon--assert '(description mushroom-grove
    "A vast underground grove of luminous mushrooms. Their blue-green glow illuminates a fairy ring of ancient stones."))
  (dungeon--assert '(description underground-lake
    "A still, black lake stretches before you. The water is perfectly mirror-smooth. Something moves in the depths."))
  (dungeon--assert '(description dark-passage
    "Impenetrable darkness. You feel cold stone walls. Something breathes heavily nearby."))
  (dungeon--assert '(description throne-room
    "A carved stone throne sits atop a dais. The walls are covered in spiral patterns—the ancient art of the Tuatha Dé Danann."))
  (dungeon--assert '(description great-hall
    "An enormous hall, pillars carved as standing warriors. At the far end, a massive figure sits wreathed in shadow—Balor of the Evil Eye."))
  (dungeon--assert '(description treasury
    "Darkness fills this sealed chamber. When lit, you see it glitters with the spoils of ages. A glass case holds something radiant."))
  (dungeon--assert '(description hidden-shrine
    "A small, sacred space. A spring bubbles up from the rock, feeding a basin carved with knotwork. The air feels holy.")))

;; ============================================================
;; Game logic helpers
;; ============================================================

(defun dungeon--player-room ()
  "Return the room the player is currently in."
  (let ((fact (cl-find-if (lambda (f)
                            (and (listp f) (eq (car f) 'at) (eq (nth 1 f) 'player)))
                          dungeon--kb)))
    (when fact (nth 2 fact))))

(defun dungeon--room-desc (room)
  "Get the description of ROOM."
  (let ((fact (cl-find-if (lambda (f)
                            (and (listp f) (eq (car f) 'description) (eq (nth 1 f) room)))
                          dungeon--kb)))
    (when fact (nth 2 fact))))

(defun dungeon--items-in-room (room)
  "Get items in ROOM."
  (cl-remove-if-not (lambda (f)
                      (and (listp f) (eq (car f) 'at-room) (eq (nth 2 f) room)))
                    dungeon--kb))

(defun dungeon--npcs-in-room (room)
  "Get NPCs in ROOM."
  (cl-remove-if-not (lambda (f)
                      (and (listp f) (eq (car f) 'at-room)
                           (eq (nth 2 f) room)
                           (cl-find-if (lambda (g)
                                         (and (listp g) (eq (car g) 'npc)
                                              (eq (nth 1 g) (nth 1 f))))
                                       dungeon--kb)))
                    dungeon--kb))

(defun dungeon--exits-from (room)
  "Get connected rooms."
  (mapcar (lambda (f) (nth 2 f))
          (cl-remove-if-not (lambda (f)
                              (and (listp f) (eq (car f) 'connects) (eq (nth 1 f) room)))
                            dungeon--kb)))

(defun dungeon--inventory ()
  "Get player inventory."
  (mapcar (lambda (f) (nth 2 f))
          (cl-remove-if-not (lambda (f)
                              (and (listp f) (eq (car f) 'has) (eq (nth 1 f) 'player)))
                            dungeon--kb)))

(defun dungeon--room-is-dark (room)
  "Check if ROOM is dark."
  (cl-find-if (lambda (f) (equal f `(dark ,room))) dungeon--kb))

(defun dungeon--can-see-p ()
  "Check if player can see (room not dark, or has light)."
  (let ((room (dungeon--player-room)))
    (or (not (dungeon--room-is-dark room))
        (dungeon--query '(player-has-light) 200))))

(defun dungeon--format-name (sym)
  "Convert symbol SYM to a display name."
  (let ((name (symbol-name sym)))
    (capitalize (replace-regexp-in-string "-" " " name))))

;; ============================================================
;; Room display
;; ============================================================

(defun dungeon--look ()
  "Describe the current room."
  (let ((room (dungeon--player-room)))
    (dungeon--emit-header (dungeon--format-name room))
    (if (dungeon--can-see-p)
        (progn
          (dungeon--emit-room (or (dungeon--room-desc room) "An unremarkable place."))
          ;; Items
          (let ((items (dungeon--items-in-room room)))
            (when items
              (dungeon--emit "")
              (dungeon--emit "You see:")
              (dolist (i items)
                (let ((item-name (nth 1 i)))
                  (unless (cl-find-if (lambda (f) (and (listp f) (eq (car f) 'npc) (eq (nth 1 f) item-name)))
                                      dungeon--kb)
                    (dungeon--emit-item (dungeon--format-name item-name)))))))
          ;; NPCs
          (let ((npcs (dungeon--npcs-in-room room)))
            (when npcs
              (dolist (n npcs)
                (let ((npc-name (nth 1 n)))
                  (if (cl-find-if (lambda (f) (equal f `(hostile ,npc-name))) dungeon--kb)
                      (dungeon--emit-fail (format "  ⚔ %s stands menacingly!" (dungeon--format-name npc-name)))
                    (dungeon--emit-npc (format "  ☘ %s is here." (dungeon--format-name npc-name))))))))
          ;; Exits
          (let ((exits (dungeon--exits-from room)))
            (dungeon--emit "")
            (dungeon--emit (format "Exits: %s"
                                   (mapconcat #'dungeon--format-name exits ", ")))))
      ;; Dark room
      (dungeon--emit-fail "It is pitch dark. You cannot see a thing.")
      (dungeon--emit "You feel exits leading away, but cannot tell where."))))

;; ============================================================
;; Actions
;; ============================================================

(defun dungeon--do-move (direction)
  "Move player to DIRECTION (a room symbol)."
  (let ((room (dungeon--player-room)))
    (if (not (member direction (dungeon--exits-from room)))
        (dungeon--emit-fail "You cannot go that way.")
      ;; Check for hostile NPCs blocking the way
      (let ((blocked nil))
        (dolist (f dungeon--kb)
          (when (and (listp f) (eq (car f) 'blocks)
                     (eq (nth 2 f) direction))
            (setq blocked (nth 1 f))))
        (if blocked
            (dungeon--emit-fail (format "%s blocks your path!" (dungeon--format-name blocked)))
          ;; Check locked
          (if (cl-find-if (lambda (f) (equal f `(locked ,direction))) dungeon--kb)
              (dungeon--emit-fail (format "%s is locked!" (dungeon--format-name direction)))
            ;; Move
            (dungeon--retract `(at player ,room))
            (dungeon--assert `(at player ,direction))
            (dungeon--emit-action (format "You travel to %s." (dungeon--format-name direction)))
            ;; Check for hostile NPC in destination
            (let ((hostiles (cl-remove-if-not
                             (lambda (f)
                               (and (listp f) (eq (car f) 'at-room)
                                    (eq (nth 2 f) direction)
                                    (cl-find-if (lambda (g) (equal g `(hostile ,(nth 1 f)))) dungeon--kb)))
                             dungeon--kb)))
              (when hostiles
                (dungeon--emit-fail "Something dangerous is here...")))
            (dungeon--look)))))))

(defun dungeon--do-take (item)
  "Take ITEM from current room."
  (let ((room (dungeon--player-room)))
    (if (not (dungeon--can-see-p))
        (dungeon--emit-fail "You can't see anything to take!")
      (if (not (cl-find-if (lambda (f) (equal f `(at-room ,item ,room))) dungeon--kb))
          (dungeon--emit-fail (format "There is no %s here." (dungeon--format-name item)))
        ;; Check if it's an NPC
        (if (cl-find-if (lambda (f) (equal f `(npc ,item))) dungeon--kb)
            (dungeon--emit-fail "You can't pick up a person!")
          (dungeon--retract `(at-room ,item ,room))
          (dungeon--assert `(has player ,item))
          (dungeon--emit-action (format "You take the %s." (dungeon--format-name item)))
          ;; Special item messages
          (cond
           ((eq item 'sword-of-light)
            (dungeon--emit-lore "The Claiomh Solais blazes with white fire! It was wielded by Nuada of the Silver Hand."))
           ((eq item 'cauldron-of-dagda)
            (dungeon--emit-lore "The Dagda's Cauldron — from it, none ever went away unsatisfied."))
           ((eq item 'lia-fail)
            (dungeon--emit-lore "The Lia Fáil, Stone of Destiny — it cries out beneath the true sovereign."))
           ((eq item 'spear-of-lugh)
            (dungeon--emit-lore "The Spear of Lugh — no battle was ever sustained against it."))
           ((eq item 'torch)
            (dungeon--emit "The torch flickers to life, casting warm shadows."))))))))

(defun dungeon--do-use (item &optional target)
  "Use ITEM, optionally on TARGET."
  (cond
   ;; Use key on locked door
   ((and item target
         (dungeon--query `(can-unlock player ,target) 200))
    (dungeon--retract `(locked ,target))
    (dungeon--emit-action (format "You unlock %s with the %s!"
                                   (dungeon--format-name target)
                                   (dungeon--format-name item))))
   ;; Use cauldron to heal
   ((and (eq item 'cauldron-of-dagda)
         (dungeon--query '(can-heal player) 200))
    (dungeon--emit-action "The cauldron glows with warm light. You feel completely restored!")
    (dungeon--assert '(healed player)))
   ;; Use Lia Fáil in throne room
   ((and (eq item 'lia-fail)
         (dungeon--query '(reveals-truth lia-fail) 200))
    (dungeon--emit-action "The Stone of Destiny cries out! A great keening fills the hall!")
    (dungeon--emit-lore "The stone reveals: Balor can only be banished by the Four Treasures united in the Great Hall.")
    (dungeon--assert '(knows-player balor-weakness)))
   ;; Use sword against fomorian
   ((and (eq item 'sword-of-light)
         target
         (cl-find-if (lambda (f) (equal f `(fomorian ,target))) dungeon--kb)
         (dungeon--query `(can-fight player ,target) 200))
    (dungeon--emit-action (format "The Sword of Light blazes! You strike at %s!"
                                   (dungeon--format-name target)))
    (if (eq target 'balor)
        (progn
          (if (dungeon--query '(has-four-treasures player) 200)
              (progn
                (dungeon--emit-header "VICTORY!")
                (dungeon--emit-lore "With the Four Treasures of the Tuatha Dé Danann united, you banish Balor back to the depths!")
                (dungeon--emit-lore "The curse is lifted. The Dún is freed.")
                (dungeon--emit "")
                (dungeon--emit "Congratulations! You have completed Dún na Sí!")
                (dungeon--assert '(game-won)))
            (dungeon--emit-fail "Balor's Evil Eye blazes! The sword alone is not enough!")
            (dungeon--emit-lore "You need all Four Treasures to defeat the Fomorian King.")))
      ;; Regular fomorian
      (dungeon--retract `(at-room ,target ,(dungeon--player-room)))
      (dungeon--retract `(hostile ,target))
      (dungeon--assert `(defeated ,target))
      (dungeon--emit-action (format "%s is vanquished!" (dungeon--format-name target)))))
   ;; Generic failure
   (t
    (if (not (member item (dungeon--inventory)))
        (dungeon--emit-fail (format "You don't have a %s." (dungeon--format-name item)))
      (dungeon--emit-fail "That doesn't seem to work.")))))

(defun dungeon--do-talk (npc)
  "Talk to NPC."
  (let ((room (dungeon--player-room)))
    (if (not (cl-find-if (lambda (f) (equal f `(at-room ,npc ,room))) dungeon--kb))
        (dungeon--emit-fail (format "%s is not here." (dungeon--format-name npc)))
      (cond
       ((eq npc 'brigid)
        (dungeon--emit-npc "Brigid speaks:")
        (cond
         ((dungeon--query '(has-four-treasures player) 100)
          (dungeon--emit-lore "You carry all Four Treasures! Go to the Great Hall and banish Balor!"))
         ((member 'sword-of-light (dungeon--inventory))
          (dungeon--emit-lore "The Claiomh Solais! You carry the Sword of Light. Seek the other Treasures."))
         ((member 'rusty-key (dungeon--inventory))
          (dungeon--emit-lore "That key... it opens the treasury to the north of the forge. Great power is sealed within."))
         (t
          (dungeon--emit-lore "Welcome, wanderer. I am Brigid, keeper of this place.")
          (dungeon--emit-lore "Four Treasures of the Tuatha Dé Danann lie hidden in this Dún.")
          (dungeon--emit-lore "The Sword of Light, the Spear of Lugh, the Cauldron of the Dagda, and the Lia Fáil.")
          (dungeon--emit-lore "Gather them all to face Balor of the Evil Eye in the Great Hall."))))
       ((cl-find-if (lambda (f) (equal f `(hostile ,npc))) dungeon--kb)
        (dungeon--emit-fail (format "%s snarls at you! It does not wish to talk." (dungeon--format-name npc))))
       (t
        (dungeon--emit-npc (format "%s has nothing to say." (dungeon--format-name npc))))))))

(defun dungeon--do-inventory ()
  "Show player inventory."
  (let ((inv (dungeon--inventory)))
    (if (not inv)
        (dungeon--emit "You carry nothing.")
      (dungeon--emit "You carry:")
      (dolist (i inv)
        (dungeon--emit-item (dungeon--format-name i))))))

(defun dungeon--do-query (goal-str)
  "Let the player query the KB directly (debug/advanced feature)."
  (let* ((goal (car (read-from-string goal-str)))
         (result (dungeon--query goal 200)))
    (if result
        (dungeon--emit (format "✓ Proved: %S" goal))
      (dungeon--emit (format "✗ Cannot prove: %S" goal)))))

;; ============================================================
;; Command parser
;; ============================================================

(defun dungeon--parse-command (input)
  "Parse INPUT string into a command."
  (let* ((words (split-string (downcase (string-trim input)) " +" t))
         (verb (intern (or (car words) "")))
         (rest (cdr words)))
    (cl-case verb
      ((n north) '(move north))
      ((s south) '(move south))
      ((e east)  '(move east))
      ((w west)  '(move west))
      ((go move) (if rest `(move-to ,(intern (car rest))) '(invalid)))
      ((look l)  '(look))
      ((take get grab) (if rest `(take ,(intern (mapconcat #'identity rest "-"))) '(invalid)))
      ((use)     (let* ((on-pos (cl-position "on" rest :test #'string=))
                        (item (if on-pos
                                  (intern (mapconcat #'identity (cl-subseq rest 0 on-pos) "-"))
                                (when rest (intern (mapconcat #'identity rest "-")))))
                        (target (when on-pos
                                  (intern (mapconcat #'identity (cl-subseq rest (1+ on-pos)) "-")))))
                   (if item `(use ,item ,target) '(invalid))))
      ((talk speak) (if rest `(talk ,(intern (mapconcat #'identity rest "-"))) '(invalid)))
      ((inventory inv i) '(inventory))
      ((help h) '(help))
      ((query prove) (if rest `(query ,(mapconcat #'identity rest " ")) '(invalid)))
      ((quit q) '(quit))
      (t '(unknown)))))

;; ============================================================
;; Command execution
;; ============================================================

(defun dungeon--execute (cmd)
  "Execute parsed command CMD."
  (setq dungeon--turn (1+ dungeon--turn))
  (let ((action (car cmd)))
    (cl-case action
      (move-to (dungeon--do-move (nth 1 cmd)))
      (look    (dungeon--look))
      (take    (dungeon--do-take (nth 1 cmd)))
      (use     (dungeon--do-use (nth 1 cmd) (nth 2 cmd)))
      (talk    (dungeon--do-talk (nth 1 cmd)))
      (inventory (dungeon--do-inventory))
      (help    (dungeon--show-help))
      (query   (dungeon--do-query (nth 1 cmd)))
      (quit    (dungeon--emit "Slán leat! (Goodbye!)")
               (dungeon--assert '(game-quit)))
      (invalid (dungeon--emit-fail "I don't understand that. Type 'help' for commands."))
      (unknown (dungeon--emit-fail "Unknown command. Type 'help' for commands.")))))

;; ============================================================
;; Help
;; ============================================================

(defun dungeon--show-help ()
  "Display help."
  (dungeon--emit-header "Commands")
  (dungeon--emit "  go <room>     - Travel to a connected room")
  (dungeon--emit "  look          - Look around")
  (dungeon--emit "  take <item>   - Pick up an item")
  (dungeon--emit "  use <item>    - Use an item")
  (dungeon--emit "  use <item> on <target> - Use item on something")
  (dungeon--emit "  talk <npc>    - Talk to someone")
  (dungeon--emit "  inventory     - Check what you carry")
  (dungeon--emit "  query <expr>  - Query the knowledge base (advanced)")
  (dungeon--emit "  help          - This message")
  (dungeon--emit "  quit          - Leave the game")
  (dungeon--emit "")
  (dungeon--emit "Room names use hyphens: crystal-cavern, dark-passage, etc."))

;; ============================================================
;; Main game loop (interactive)
;; ============================================================

(defun dungeon--prompt ()
  "Prompt for and execute one command."
  (unless (or (cl-find-if (lambda (f) (equal f '(game-won))) dungeon--kb)
              (cl-find-if (lambda (f) (equal f '(game-quit))) dungeon--kb))
    (let ((input (read-string
                  (format "[Turn %d] > " dungeon--turn))))
      (push input dungeon--history)
      (dungeon--emit "")
      (dungeon--execute (dungeon--parse-command input))
      (dungeon--prompt))))

;;;###autoload
(defun dungeon-start ()
  "Start the dungeon crawl game."
  (interactive)
  (switch-to-buffer (get-buffer-create dungeon--buffer))
  (erase-buffer)
  (dungeon--init-rules)
  (dungeon--init-world)
  (dungeon--emit "")
  (dungeon--emit "╔══════════════════════════════════════════════╗")
  (dungeon--emit "║         D Ú N   N A   S Í                    ║")
  (dungeon--emit "║    The Mound of the Fair Folk                ║")
  (dungeon--emit "║                                              ║")
  (dungeon--emit "║  A FOL-Powered Dungeon Crawl                 ║")
  (dungeon--emit "║  Powered by emacs-atp theorem prover         ║")
  (dungeon--emit "╚══════════════════════════════════════════════╝")
  (dungeon--emit "")
  (dungeon--emit-lore "In the time before time, the Tuatha Dé Danann brought")
  (dungeon--emit-lore "Four Treasures to Ireland: the Sword of Light, the Spear")
  (dungeon--emit-lore "of Lugh, the Cauldron of the Dagda, and the Lia Fáil.")
  (dungeon--emit-lore "Now Balor of the Evil Eye has seized the ancient Dún.")
  (dungeon--emit-lore "Only the Four Treasures united can banish him.")
  (dungeon--emit "")
  (dungeon--look)
  (dungeon--emit "")
  (dungeon--emit "(Type 'help' for commands)")
  (dungeon--prompt))

(provide 'atp-dungeon)
;;; atp-dungeon.el ends here
