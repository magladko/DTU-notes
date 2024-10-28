## Introduction
General course objectives 

The purpose of the course is to introduce students to technologies for creating scalable startups leveraging the potential of generative AI, by utilizing high level application frameworks to simulate design concepts as a basis for assessing their business potential as well as societal impact.

During the course we will explore the underlying reasoning capabilities provided by transformer and diffusion based models, and map these abilities to novel value propositions structured as course assignments, using EPFL's business modeling tool "The market opportunity navigator" and MIT's "Disciplined entrepreneurship" approach.

## Week 1
AI simulation : Transformer models

Interactive model of GPT-2 transformer architecture running locally in browser, makes it possible to explore how large language model (LLM) components of input text tokenization, vector embeddings, self-attention mechanism, MLP multilayer perceptron feedforward network, and output layer interact to predict the next token in a sequence.

Project 1 use case : Digital twin + LLM

Combining digital twin virtual representations with LLMs may revolutionize how companies operate, as transformers are able to reason about the generated data, and provide a multimodal interface to simulate how people and objects interact to improve products and optimize workflows. This week's edition of Economist features articles describing some of the digital twin + AI use cases: /content/enforced/215232-DTU_e24_38113/Digital twins are making companies more efficient.pdf , /content/enforced/215232-DTU_e24_38113/Digital twins are enabling scientific innovation.pdf

Assignment 1 : Part 1  Market opportunity (hand-in 22/9 2024) 

Team up with your AI sidekick from 9 to 11 who will help you translate GPT2 functionalities into digital twin features which are in turn mapped to products (you will receive an invite with URL). Please return to the auditorium at 11:15 to briefly present some of the concepts you defined. EPFL's business modeling tool is a 3 step process for identifying market opportunities and assess the potential against the challenges of implementation. We focus in week 1 on the first step where the goal is to identify core technical abilities based on the "digital twin + LLM" use case, and map them into potential market opportunities. Initially use worksheet 1 to describe functional properties of technical elements separate from any envisioned products. Subsequently add how these core abilities could be combined into multiple products, offering market opportunities for targeting different segments, and enclose the worksheet as first part of the project 1 assignment.

## Week 2
AI simulation : Transformer models

Explore prompt engineering techniques using the Mistral API to make the LLM classify and extract information using few shot learning, and create personalized responses for a customer service bot. Build a chatbot conversational interface using the OpenAI API . Start by watching the short videos, subsequently run the Jupyter notebook code cells in the left pane of the browser. Then check out how Prompt Poet recently acquired by Google, combines templates with few shot learning and integrates external data to simplify prompt design. If you are new to Python watch this 5 mins intro on building LLM prompts with variables. 

Project 1 use case : Digital twin + LLM

Microsoft's recent report on how AI is reshaping work indicates a rapidly increasing individual uptake as many people bring their own tools, whereas companies miss out on the benefits by not strategically integrating AI at scale. McKinsey suggests it would be useful to think of digital twins as labs, which based on data simulate real world scenarios making it possible to reimagine workflows and processes. Extending digital twins with LLMs enable even non technical users to interact with highly complex systems through conversational interfaces.

Assignment 1 : Part 2  Potential and challenges (hand-in 22/9 2024) 

EPFL's business modeling tool is a 3 step process for identifying market opportunities and assess the potential against the challenges of implementation. We focus in week 2 on the second step where the goal is to select the identified market opportunities in the "digital twin + LLM" use case, and consider the potential versus the challenges for implementation. Use worksheet 2 to break down the potential into sub questions by considering reasons to buy, market volume and margins. Likewise for challenges  assess product development difficulties, time to market and threats from competitors, and enclose the worksheet as second part of the project 1 assignment.

## Week 3
AI simulation : Transformer models

Explore how to extend LLMs with different tools using the Mistral API for function calling which could enable models to interact with digital twins, and potentially leverage any software as a service SaaS exposed through cloud APIs. Likewise, implementing  RAG enables LLMs to chunk up documents and encode them as embeddings, which in turn allows the model to search and retrieve relevant information for reasoning and generating new content. Essentially enabling you to create a conversational interface to chat with any external document.

Assignment 1 : Part 3  Agile strategy  (hand-in 22/9 2024) 

EPFL's business modeling tool is a 3 step process for identifying market opportunities,  assess which are the most attractive and when to pursue them. We focus in week 3 on the third step where the goal is to consider which market opportunities offer the best growth or backup options based on their potential identified in the "digital twin + LLM" use case. Use worksheet 3 to assess how related the products and customer needs are in order to decide which market opportunities to pursue now or reserve for pivoting,  and enclose the worksheet as the third part of the project 1 assignment.

## Week 4
AI simulation : Agentic reasoning

Explore how to extend LLMs with ReAct agents capable of reasoning by having access to tools that enable them to search for information and consider the relevance of what is retrieved in order to generate new content. Constructing agents from graphs consisting of nodes and edges facilitates designing their "think step by step" reasoning. This notebook code provides an example of building an agent using LangGraph and Pinecone integrated with OpenAI's API, which is explained in detail in the accompanying video.

Project 2 use case : Digital twin + agentic reasoning

Extending LLMs with agentic reasoning conceptualized as nodes and edges in a graph could offer a framework for agents to interact with digital twin virtual representations. Essentially, allowing agents to dynamically decide which functions to call when interacting with digital twin sequences of actions and decisions, and reflect on the outcomes in order to build simulations improving processes or workflows. The LangGraph Studio provides an app for sketching out the graph structure for a ReAct agent framework that could interacting with a digital twin virtual representation of actions and decisions in order to predict next token event in a sequence. 

Assignment 2 Week 4 : Combining features into products  (hand-in 13/10 2024) 

Team up with your AI sidekick from 9 to 11 using app.aethena.ai to sketch out ReAct agent "thought, act, observe" abilities for LLMs to interact with digital twin concepts. EPFL's business modeling tool is a 3 step process for identifying market opportunities,  assess which are the most attractive and when to pursue them. We focus in week 4 again on the first step where the goal is to identify ReAct capabilities for the "digital twin + agentic reasoning" use case, and map them into potential market opportunities.  Initially use worksheet 1 to describe the LLM agentic reasoning abilities separate from envisioned products. Subsequently add how these core abilities could be combined into multiple products, offering market opportunities for targeting different segments, and enclose the worksheet as first part of the project 2 assignment. 

## Week 5
AI simulation : Agentic reasoning

Explore how to extend LLMs with multiple agents that collaborate on producing content by defining separate roles and tasks for each of them. This tutorial consists of a notebook implementing the agent workflow using LangGraph including an interface for generating content, as well as a video explaining the code.

Project 2 use case : Digital twin + agentic reasoning

Extending LLMs with agentic reasoning conceptualized as nodes and edges in a graph could offer a framework for agents to interact with digital twin virtual representations. Essentially, allowing agents to dynamically decide which functions to call when interacting with digital twin sequences of actions and decisions, and reflect on the outcomes in order to build simulations improving processes or workflows. The LangGraph Studio provides an app for sketching out the graph structure for a ReAct agent framework that could interacting with a digital twin virtual representation of actions and decisions in order to predict next token event in a sequence. 

Assignment 2 Week 5 : Mapping potential vs. challenges  (hand-in 13/10 2024) 

Team up with your AI sidekick from 9 to 11 using app.aethena.ai to sketch out how multiple agents with specific roles and tasks could collaborate to interact with digital twin concepts. EPFL's business modeling tool is a 3 step process for identifying market opportunities,  assess which are the most attractive and when to pursue them. We focus in week 5 again on the second step of mapping the potential versus challenges when applying a team of agents to the "digital twin + agentic reasoning" use case.  Initially use worksheet 2 to assess the underlying parameters to compare alternative market opportunities , and enclose the worksheet as second part of the project 2 assignment. Likewise use the LangGraph Studio app to sketch out your collaborative agent framework and save the generated code for the project 2 assignment.

## Week 6
AI simulation : Agentic reasoning

Explore how to enable agent frameworks to interact with digital twins represented as knowledge graphs that can be learned by the LLM. Transforming the digital twin generated data into entities and relations improves the ability of the LLM to link and retrieve information at multiple levels within a network structure. Likewise, extending the encoded nodes and edges with natural language descriptions could allow the LLM to reason about the digital twin generated data and predict the next token in sequences reflecting workflows. 

Project 2 use case : Digital twin + agentic reasoning

Extending LLMs with agentic reasoning conceptualized as nodes and edges in a graph could offer a framework for agents to interact with digital twin virtual representations. Essentially, allowing agents to dynamically decide which functions to call when interacting with digital twin sequences of actions and decisions, and reflect on the outcomes in order to build simulations improving workflows. Such processes could be represented as knowledge graphs consisting of nodes describing people or assets linked by edges defining their relationships to other entities. An LLM can automatically extract these elements from text or data to construct graphs which in turn makes it possible to query and reason about the structures that define digital twin representations using natural language. 

Assignment 2 Week 6 : Defining an agile strategy  (hand-in 13/10 2024) 

Team up with your AI sidekick from 9 to 11 using app.aethena.ai to translate aspects of your digital twin concepts into knowledge graph entities linked by edges defining how the components reflect structural relations like e.g. PART_OF or NEXT to define temporal sequences. Reasoning about these relations might enable an LLM to predict the next token representing actions or decisions in a digital twin workflow. EPFL's business modeling tool is a 3 step process for identifying market opportunities,  assess which are the most attractive and when to pursue them. We focus in week 6 again on the third step of defining an agile strategy for applying a team of agents to the "digital twin + agentic reasoning" use case.  Initially use worksheet 3 to assess the underlying parameters to compare alternative market opportunities, and enclose the worksheet as third part of the project 2 assignment.