#version 330 core

const vec2 uvs[16] = vec2[16](
  vec2(0, 0), vec2(0.5, 0), vec2(0, 0.5), vec2(0.5, 0.5),
  vec2(0.5, 0), vec2(1, 0), vec2(0.5, 0.5), vec2(1, 0.5),
  vec2(0, 0.5), vec2(0, 1), vec2(0.5, 0.5), vec2(0.5, 1),
  vec2(0.5, 0.5), vec2(0.5, 1), vec2(1, 1), vec2(1, 0.5)
);

//vectors for the horiziontal/vertical directions to expand the quad in
const vec2 dirs[4] = vec2[4](
  vec2(0, 0),
  vec2(0, -1),
  vec2(1, 0),
  vec2(1, -1)
);

const vec4 up = vec4(0, 1, 0, 0);
const vec4 right = vec4(1, 0, 0, 0);
const ivec2 dim = ivec2(64, 16);
const vec2 char_dim = vec2(2.f / dim.x, 2.f / dim.y);

layout(location = 0) in ivec2 pos;
layout(location = 1) in int tex_idx;

out vec2 fuv;

void main(void){
  fuv = uvs[4 * tex_idx + gl_VertexID];
  //Scale positions into NDC and flip y to put 0,0 at top-left
  float x = pos.x * char_dim.x - 1;
  float y = -1 * (pos.y * char_dim.y - 1);
  vec4 p = vec4(x, y, 0, 1);
  gl_Position = p + char_dim.x * right * dirs[gl_VertexID].x + char_dim.y * up * dirs[gl_VertexID].y;
}
