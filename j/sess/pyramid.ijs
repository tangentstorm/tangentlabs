NB. pascal''s pyramid

14:17:55 tangentstorm [ ,./|.blit |:#:!/~i.8
14:17:56 j-bot tangentstorm: ▙
14:17:56 j-bot tangentstorm: ▙▙  ▐▖
14:17:56 j-bot tangentstorm: ▙ ▙  ▙  ▐▀▖  ▄
14:17:56 j-bot tangentstorm: ▙▙▙▙▐▚▛▖▐▛▜▖ ▘▘  ▞▗  ▗▖
14:19:08 tangentstorm ^ successive cross sections of the bits of pascal's triangle.
14:19:41 tangentstorm (stack them up to make a pyramid)
14:19:58 tangentstorm so the two bits on the right there are the high bits of the
                      number 35
14:23:23 tangentstorm [  ,./|.blit 1|: 0|: |:#:!/~i.8
14:23:24 j-bot tangentstorm:  ▞▚  ▗
14:23:24 j-bot tangentstorm: ▗▖▗▖▗▙▙ ▗▀▖ ▗▄
14:23:24 j-bot tangentstorm: ▟▟▙▙▞▌▛▖▄▀▄ ▖▘▖ ▟▙  ▞▖  ▄   ▖
14:23:56 tangentstorm if the first one is a top down view, then these are the cross
                      sections of the front view.
14:24:13 tangentstorm leftmost is closest, rightmost is further away.
14:24:42 tangentstorm [ blit +./ 1|: 0|: |:#:!/~i.8
14:24:43 j-bot tangentstorm:  ▟▚
14:24:43 j-bot tangentstorm: ▗█▙▖
14:24:43 j-bot tangentstorm: ▟██▙
14:25:04 tangentstorm composite image. so this is what you'd actually see orthogonal
projection from the front.
14:25:57 tangentstorm and from the top:
14:25:59 tangentstorm [ blit +./ |:#:!/~i.8
14:25:59 j-bot tangentstorm: ▙
14:25:59 j-bot tangentstorm: █▙
14:25:59 j-bot tangentstorm: ██▙
14:25:59 j-bot tangentstorm: ███▙
14:27:28 tangentstorm [ blit 2| +/ |:#:!/~i.8  NB. still looking top down, height mod
2
14:27:29 j-bot tangentstorm: ▙
14:27:29 j-bot tangentstorm: ▛▚
14:27:29 j-bot tangentstorm: ▛▝▚
14:27:29 j-bot tangentstorm: ▙▄▄▙
14:32:45 tangentstorm haha
14:32:47 tangentstorm check this out
14:32:52 tangentstorm [ blit _8 {. {: |:#:!/~i.64
14:32:52 j-bot tangentstorm: ▙   ▙   ▙ ▗▀    ▝▘▖ ▙   ▙   ▙
14:32:53 j-bot tangentstorm: ▙▙  ▙▙  ▙▙▖        ▗▙▙  ▙▙  ▙▙
14:32:53 j-bot tangentstorm: ▙ ▙ ▙ ▙ ▌▘           ▘▚ ▙ ▙ ▙ ▙
14:32:53 j-bot tangentstorm: ▙▙▙▙▙▙▙▙▙▖            ▗▙▙▙▙▙▙▙▙▙
14:33:30 tangentstorm 50 points to anyone who can guess what that is. :)
