
<img width="1024" height="1024" alt="unnamed (1)" src="https://github.com/user-attachments/assets/3d3a6948-453c-4630-99aa-a6dd52adc2ae" />

# When to Listen and When to Forget: A Guide to Chatbot Context

When we build a chatbot, we face a common problem. A user asks about the weather. A few minutes later, they ask to book a hotel. But the bot, still stuck on the weather, gets confused. It fails to see that the topic has changed.

This is a classic failure of context. Getting this right is the key to building a bot that feels smart and helpful instead of frustrating. The core challenge is simple: how do we use conversation history without letting it trap our bot in the past?

## The Double-Edged Sword of Memory

First, we have to decide if we should use conversation history at all.

Sometimes, history is essential. If a user says, "Yes, please do," we need the previous messages to know what they are agreeing to. But for a new, self-contained query like, "How tall is Mount Everest?", old context just adds noise. It can even trick our model into making a mistake.

A good rule of thumb is to look at the last two or three messages. This gives the bot enough memory to understand follow-up questions but not so much that it gets stuck. The real secret, however, isn't about *how much* history to use, but *when* to use it.

## Reset Detection: Your Bot's "Forget" Button

To solve this, we need a "forget" button for our bot. In machine learning, this is called **reset detection**. The goal is to figure out if a new message continues the last topic or starts a fresh one.

Placing this check at the very beginning of your pipeline, *before* you try to classify the intent, is the most important step. If you classify the intent first, you risk using the wrong context, wasting resources, and getting the wrong answer.

Think of it as a gatekeeper. Before your bot does anything else, it asks one question: "Is this a new conversation?"

## How to Build a Reset Detector

There are several ways to build this gatekeeper, from simple rules to complex models.

* **Check for Distance:** The simplest way is to compare the new message to the old ones. We can use embeddings to turn the text into numbers and measure the cosine similarity between them. If the similarity is low, it means the topics are very different. We declare a "reset" and treat the message as brand new. This is fast but requires careful tuning of the similarity threshold.

* **Use a Simple Classifier:** We can train a small, dedicated model for this one job. It’s a binary classifier that only answers "yes" or "no" to the question: "Does this message depend on the previous one?" This needs labeled data but is often more accurate than a simple distance check.

* **Apply Smart Rules (Heuristics):** Some of the strongest signals aren't in the text itself.
    * **Time Gaps:** A long pause between messages is a huge clue that the user is starting fresh.
    * **Keywords:** Words like "anyway," "new topic," or "forget that" are explicit signs of a reset.
    * **Conversation Openers:** Greetings like "hi" or "can you help me" almost always signal a new start.

* **Ask a Larger Model:** For tricky cases, you can prompt an LLM with a simple question: "Does this message continue the last topic or start a new one?" This is slower and more expensive but very effective for nuanced situations.

In practice, the best systems mix these approaches. They might use a fast distance check first and then confirm with a few simple rules.

## Better to Forget Than to Misunderstand

No reset detector is perfect. It will make mistakes. So, which mistake is safer?

1.  **A false positive:** The bot thinks the topic changed, but it didn't. The user might have to repeat a small piece of information.
2.  **A false negative:** The bot thinks the topic is the same, but it changed. The bot gives a completely wrong, out-of-context answer.

The second mistake is far worse. It breaks the user's trust and ends the conversation. It is always safer to start fresh than to be confidently wrong.

By building a solid reset detector and placing it at the front of your process, you can solve one of the biggest problems in conversational AI. You allow your bot not just to remember, but also to know when it’s time to forget.
