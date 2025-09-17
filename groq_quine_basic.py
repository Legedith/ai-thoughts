import os
from pathlib import Path

from dotenv import load_dotenv
from groq import Groq


def main() -> None:
    load_dotenv()

    api_key = os.environ.get("GROQ_API_KEY")
    if not api_key:
        raise RuntimeError("Missing GROQ_API_KEY in environment")

    model = os.environ.get("GROQ_MODEL", "llama-3.1-8b-instant")

    client = Groq(api_key=api_key)

    source_code = Path(__file__).read_text(encoding="utf-8")
    prompt = (
        "You are a strict echo bot.\n"
        "Return EXACTLY the text between <<BEGIN>> and <<END>> with no changes.\n"
        "Do not add code fences, commentary, or extra whitespace.\n"
        "<<BEGIN>>\n"
        f"{source_code}\n"
        "<<END>>"
    )

    chat_completion = client.chat.completions.create(
        messages=[{"role": "user", "content": prompt}],
        model=model,
        temperature=0,
    )

    print(chat_completion.choices[0].message.content)


if __name__ == "__main__":
    main()


